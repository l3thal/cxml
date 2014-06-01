(in-package :cxml)

(defparameter *self-closers* '("br" "img" "meta" "hr" "input" "link" "col"))
(defparameter *bad-closers* '(("icon" "i")))
(defparameter *parent-closers* '(("li" "ul" "ol")))

(defun p/element (input)
  (multiple-value-bind (cat n-b new-b uri lname qname attrs) (p/sztag input)
    (sax:start-element (handler *ctx*) uri lname qname attrs)
    (let* ((h (handler *ctx*))
	   (es (rune-dom::element-stack h))
	   (tag (dom:tag-name (car es))))
      (when (and (eq cat :stag)
		 ;; REDONE: handle strangness with some tags not having end tags
		 ;;         so dont read content as there is none there
		 (not (member tag *self-closers* :test #'string-equal)))
	(let ((*namespace-bindings* n-b))
	  ;; REDONE: loop and gather dead self closer end tags until you reach correct tag
	  ;;         if that correct tag is bad nested closer, close current tag and bail
	  ;;         if the current tag is a bad closer then close it out and kill bad ending tag
	  (loop
	     (multiple-value-bind (cat2 sem2) (p/content input)
	       (cond ((and (eq cat2 :etag)
			   (string-equal tag (car sem2)))
		      (p/etag input qname)
		      (return))
		     ((and (assoc qname *parent-closers* :test #'string-equal)
			   (member (car sem2) (assoc qname *parent-closers* :test #'string-equal) :test #'string-equal))
		      (return))
		     ((or (member (car sem2) *self-closers* :test #'string-equal)
			  (and (assoc qname *bad-closers* :test #'string-equal)
			       (member (car sem2) (assoc qname *bad-closers* :test #'string-equal) :test #'string-equal)))
		      (read-token input))
		     (t (return))))))))
    (sax:end-element (handler *ctx*) uri lname qname)
    (undeclare-namespaces new-b)
    (pop (base-stack *ctx*))
    (validate-end-element *ctx* qname)))

(defmethod sax:start-element ((sink sink) namespace-uri local-name qname attributes)
  (declare (ignore namespace-uri local-name))
  (maybe-close-tag sink)
  (when (stack sink)
    (incf (tag-n-children (first (stack sink)))))
  (push (make-tag qname) (stack sink))
  (when (indentation sink)
    (sink-fresh-line sink)
    (start-indentation-block sink))
  (sink-write-rune #/< sink)
  (sink-write-rod qname sink)
  (dolist (a (if (canonical sink)
		 (sort (copy-list attributes)
		       #'rod<
		       :key #'sax:attribute-qname)
		 attributes))
    (sink-write-rune #/space sink)
    (sink-write-rod (sax:attribute-qname a) sink)
    (sink-write-rune #/= sink)
    (sink-write-rune #/\" sink)
    (if (canonical sink)
	(sink-write-escapable-rod/canonical (sax:attribute-value a) sink)
	;; REDONE dont write escaped attributes or entities just write as is
	(sink-write-rod (sax:attribute-value a) sink)
	;; (sink-write-escapable-rod/attribute (sax:attribute-value a) sink)
	)
    (sink-write-rune #/\" sink))
  ;; REDONE: always open/close these tags, not self close tags
  ;;         eg, <script /> becaome <script></script> instead
  (when (or (canonical sink)
	    (not (member qname *self-closers* :test #'string-equal)))
    (maybe-close-tag sink)))

(defun read-token-after-|<| (zinput input)
       (let ((d (read-rune input))
	     (element (car (rune-dom::element-stack (handler *ctx*)))))
	 (cond ((eq d :eof)
		(eox input "EOF after '<'"))
	       ;; REDONE: treat all data in script tag as cdata
	       ((and (dom:element-p element)
		     (string-equal "script" (dom:tag-name element)))
		(if (rune= #// d)
		    (multiple-value-bind (kind tag) (read-tag-2 zinput input :etag)
		      (if (string-equal "script" (car tag))
			  (values kind tag)
			  (progn
			    (values :CDATA (format nil "</~a>" (car tag)))
			    ;; (unread-rune d input)
			    ;; (values :CDATA (read-cdata input))
			    )))
		    (progn
		      (unread-rune d input)
		      (values :CDATA (format nil "<~a" (read-cdata input))))))
	       ((rune= #/! d)
		(read-token-after-|<!| input))
	       ((rune= #/? d)
		(multiple-value-bind (target content) (read-pi input)
		  (cond ((rod= target '#.(string-rod "xml"))
			 (values :xml-decl (cons target content)))
			((rod-equal target '#.(string-rod "XML"))
			 (wf-error zinput
				   "You lost -- no XML processing instructions."))
			((and sax:*namespace-processing* (position #/: target))
			 (wf-error zinput
				   "Processing instruction target ~S is not a ~
                               valid NcName."
				   (mu target)))
			(t
			 (values :PI (cons target content))))))
	       ((eq *data-behaviour* :DTD)
		(unread-rune d input)
		(unless (or (rune= #// d) (name-start-rune-p d))
		  (wf-error zinput "Expected '!' or '?' after '<' in DTD."))
		(values :seen-< nil))
	       ((rune= #// d)
		(let ((c (peek-rune input)))
		  (cond ((name-start-rune-p c)
			 (read-tag-2 zinput input :etag))
			(t
			 (wf-error zinput
				   "Expecting name start rune after \"</\".")))))
	       ((name-start-rune-p d)
		(unread-rune d input)
		(read-tag-2 zinput input :stag))
	       (t
		(wf-error zinput "Expected '!' or '?' after '<' in DTD.")))))

(defun read-token-3 (zinput)
  (let ((input (car (zstream-input-stack zinput))))
    ;; PI Comment
    (let ((c (read-rune input)))
      (cond
	;; first the common tokens
	((rune= #/< c)
	 (read-token-after-|<| zinput input))
	;; now dispatch
	(t
	 (ecase *data-behaviour*
	   (:DTD
	    (cond ((rune= #/\[ c) :\[)
		  ((rune= #/\] c) :\])
		  ((rune= #/\( c) :\()
		  ((rune= #/\) c) :\))
		  ((rune= #/\| c) :\|)
		  ((rune= #/\> c) :\>)
		  ((rune= #/\" c) :\")
		  ((rune= #/\' c) :\')
		  ((rune= #/\, c) :\,)
		  ((rune= #/\? c) :\?)
		  ((rune= #/\* c) :\*)
		  ((rune= #/\+ c) :\+)
		  ((name-rune-p c)
		   (unread-rune c input)
		   (values :nmtoken (read-name-token input)))
		  ((rune= #/# c)
		   (let ((q (read-name-token input)))
		     (cond ((rod= q '#.(string-rod "REQUIRED")) :|#REQUIRED|)
			   ((rod= q '#.(string-rod "IMPLIED")) :|#IMPLIED|)
			   ((rod= q '#.(string-rod "FIXED"))   :|#FIXED|)
			   ((rod= q '#.(string-rod "PCDATA"))  :|#PCDATA|)
			   (t
			    (wf-error zinput "Unknown token: ~S." q)))))
		  ((or (rune= c #/U+0020)
		       (rune= c #/U+0009)
		       (rune= c #/U+000D)
		       (rune= c #/U+000A))
		   (values :S nil))
		  ((rune= #/% c)
		   (cond ((name-start-rune-p (peek-rune input))
			  ;; an entity reference
			  (read-pe-reference zinput))
			 (t
			  (values :%))))
		  (t
		   (wf-error zinput "Unexpected character ~S." c))))
	   (:DOC
	    (cond
	      ((rune= c #/&)
	       ;; REDONE fix entities, basically ignore them
	       (values :CDATA "&")
	       ;; (multiple-value-bind (kind data) (read-entity-like input)
	       ;; 	 (cond ((eq kind :ENTITY-REFERENCE)
	       ;; 		(values :ENTITY-REF data))
	       ;; 	       ((eq kind :CHARACTER-REFERENCE)
	       ;; 		(values :CDATA
	       ;; 			(with-rune-collector (collect)
	       ;; 			  (%put-unicode-char data collect))))))
	       )
	      (t
	       (unread-rune c input)
	       (values :CDATA (read-cdata input)))))))))))

(defun read-att-value-2 (input)
  (with-rune-collector-4 (collect)
    (let ((delim (read-rune input)))
      (when (eql delim :eof)
	(eox input))
      ;; REDONE handle entity as delim instead of ' "
      (if (rune= #/& delim)
      	  (read-entity-like input))
      (unless (member delim '(#/\" #/\' #/&) :test #'eql)
	;; REDONE put back value, it might not be a delimeted attribute value
	(unread-rune delim input)
	(setf delim #\space)
        ;; (wf-error input
	;; 	  "Bad attribute value delimiter ~S, must be either #\\\" or #\\\'."
	;; 	  (rune-char delim))
	)
      (loop
	 (let ((c (read-rune input)))
	   (cond ((eq c :eof)
		  (eox input "EOF"))
		 ((rune= c delim)
		  ;; REDONE handle entity delim, end using the delim if its entity
		  (when (rune= #/& delim)
		    (read-entity-like input))
		  (return))
		 ((rune= c #/<)
		  (wf-error input "'<' not allowed in attribute values"))
		 ;; REDONE fix entities inside properties, ignore entities inside attrs
		 ;; Not needed because of above
		 ;; ((rune= #/& c)
		 ;;  (multiple-value-bind (kind sem) (read-entity-like input)
		 ;;    (ecase kind
		 ;;      (:CHARACTER-REFERENCE
		 ;;       (%put-unicode-char sem collect))
		 ;;      (:ENTITY-REFERENCE
		 ;;       (let* ((exp (internal-entity-expansion sem))
		 ;;              (n (length exp)))
		 ;;         (declare (type (simple-array rune (*)) exp))
		 ;;         (do ((i 0 (%+ i 1)))
		 ;;             ((%= i n))
		 ;;           (collect (%rune exp i))))))))
		 ;; REDONE dont check this as attributes may have no delimiter and thus space based
		 ;; ((space-rune-p c)
		 ;;  (collect #/u+0020))
		 ;; REDONE check for end tag in case a space demlim attribute reaches end of open tag
		 ((rune= #/> c)
		  (unread-rune c input)
		  (return))
		 (t
		  (collect c))))))))

(defmethod sax:characters ((sink sink) data)
  (maybe-close-tag sink)
  (cond
    ((and (eq (car (stack sink)) :cdata)
          (not (canonical sink))
          (not (search #"]]" data)))
     (when (indentation sink)
       (sink-fresh-line sink))
     (sink-write-rod #"<![CDATA[" sink)
     ;; XXX signal error if body is unprintable?
     ;; zzz no, in that case, split into multiple CDATA sections
     (map nil (lambda (c) (sink-write-rune c sink)) data)
     (sink-write-rod #"]]>" sink))
    (t
     (if (indentation sink)
	 (unparse-indented-text data sink)
	 (if (canonical sink)
	     (sink-write-escapable-rod/canonical data sink)
	     ;; REDONE: dont escape and use entities
	     (sink-write-rod data sink)
	     ;; no longer needed because of above
	     ;; (sink-write-escapable-rod data sink)
	     )))))

(defun read-attribute-list (zinput input imagine-space-p)
  (cond ((or imagine-space-p
             (let ((c (peek-rune input)))
	       (not (eq c :eof))))
	 ;; REDONE: remove "," and treat as space
	 (until (or (eq :eof (peek-rune input))
		    (rune= #/> (peek-rune input))
		    (name-start-rune-p (peek-rune input)))
	   (consume-rune input))
	 ;; no longer needed because of above
	 ;; (read-S? input)
         (cond ((eq (peek-rune input) :eof)
                nil)
               ((name-start-rune-p (peek-rune input))
		(cons (read-attribute zinput input)
		      (read-attribute-list zinput input nil)))
               (t
                nil)))
        (t
         nil)))

(defun read-attribute (zinput input)
  (unless (name-start-rune-p (peek-rune input))
    (wf-error zinput "Expected name."))
  ;; arg thanks to the post mortem nature of name space declarations,
  ;; we could only process the attribute values post mortem.
  (let ((name (read-name-token input)))
    (while (let ((c (peek-rune input)))
             (and (not (eq c :eof))
                  (or (rune= c #/U+0020)
                      (rune= c #/U+0009)
                      (rune= c #/U+000A)
                      (rune= c #/U+000D))))
      (consume-rune input))
    (unless (eq (read-rune input) #/=)
      ;; REDONE return wondering attribute instead of erroring out
      ;;        unread the latest rune as well while doing this
      (unread-rune #// input)
      (return-from read-attribute (cons name "true"))
      ;;(return-from read-attribute (cons name "true"))
      ;; (wf-error zinput "Expected \"=\".")
      )
    (while (let ((c (peek-rune input)))
             (and (not (eq c :eof))
                  (or (rune= c #/U+0020)
                      (rune= c #/U+0009)
                      (rune= c #/U+000A)
                      (rune= c #/U+000D))))
      (consume-rune input))
    (cons name (read-att-value-2 input))))

(defun p/content (input)
  ;; [43] content ::= (element | CharData | Reference | CDSect | PI | Comment)*
  (loop
     (multiple-value-bind (cat sem) (peek-token input)
       (case cat
	 ((:stag :ztag)
	  (p/element input))
	 ((:CDATA)
	  (process-characters input sem)
	  (sax:characters (handler *ctx*) sem))
	 ((:ENTITY-REF)
	  (let ((name sem))
	    (consume-token input)
	    (recurse-on-entity input name :general
			       (lambda (input)
				 (prog1
				     (etypecase (checked-get-entdef name :general)
				       (internal-entdef (p/content input))
				       (external-entdef (p/ext-parsed-ent input)))
				   (unless (eq (peek-token input) :eof)
				     (wf-error input "Trailing garbage. - ~S"
					       (peek-token input))))))))
	 ((:<!\[)
	  (let ((data (process-cdata-section input)))
	    (sax:start-cdata (handler *ctx*))
	    (sax:characters (handler *ctx*) data)
	    (sax:end-cdata (handler *ctx*))))
	 ((:PI)
	  (consume-token input)
	  (sax:processing-instruction (handler *ctx*) (car sem) (cdr sem)))
	 ((:COMMENT)
	  (consume-token input)
	  (sax:comment (handler *ctx*) sem))
	 (otherwise
	  ;; REDONE: added return values so I can check things
	  ;; (return)
	  (return (values cat sem)))))))

(defun process-characters (input sem)
  (consume-token input)
  ;; REDONE dont check this
  ;; (when (search #"]]>" sem)
  ;;   (wf-error input "']]>' not allowed in CharData"))
  (validate-characters *ctx* sem))

(defun p/doctype-decl (input &optional dtd-extid)
  (let ()
    (let ((*expand-pe-p* nil)
          name extid)
      (expect input :|<!DOCTYPE|)
      (p/S input)
      (setq name (p/nmtoken input))
      (when *validate*
        (setf (model-stack *ctx*) (list (make-root-model name))))
      (when (eq (peek-token input) :S)
        (p/S input)
        (unless (or (eq (peek-token input) :\[ )
                    (eq (peek-token input) :\> ))
          (setf extid (p/external-id input t))))
      (when dtd-extid
        (setf extid dtd-extid))
      (p/S? input)
      (sax:start-dtd (handler *ctx*)
                     name
                     (and extid (extid-public extid))
                     (and extid (uri-rod (extid-system extid))))
      (when (eq (peek-token input) :\[ )
        (when (disallow-internal-subset *ctx*)
          (wf-error input "document includes an internal subset"))
        (ensure-dtd)
        (consume-token input)
	(sax:start-internal-subset (handler *ctx*))
        (while (progn (p/S? input)
                      (not (eq (peek-token input) :\] )))
          (if (eq (peek-token input) :PE-REFERENCE)
              (let ((name (nth-value 1 (read-token input))))
                (recurse-on-entity input name :parameter
                                   (lambda (input)
                                     (etypecase (checked-get-entdef name :parameter)
                                       (external-entdef
                                        (p/ext-subset input))
                                       (internal-entdef
                                        (p/ext-subset-decl input)))
                                     (unless (eq :eof (peek-token input))
                                       (wf-error input "Trailing garbage.")))))
              (let ((*expand-pe-p* t))
                (p/markup-decl input))))
        (consume-token input)
	(sax:end-internal-subset (handler *ctx*))
        (p/S? input))
      (expect input :>)
      (when extid
        (let* ((effective-extid
                (extid-using-catalog (absolute-extid input extid)))
               (sysid (extid-system effective-extid))
               (fresh-dtd-p (null (dtd *ctx*)))
               (cached-dtd
		;; REDONE dont try and figure anything out about dtd
                (and nil
		     fresh-dtd-p
                     (not (standalone-p *ctx*))
                     (getdtd sysid *dtd-cache*))))
          (cond
            (cached-dtd
	     (setf (dtd *ctx*) cached-dtd)
	     (report-cached-dtd cached-dtd))
            (t
	     (ensure-dtd)
	     ;; REDONE ignore doctype and dont process it at all
	     ;; (let ((xi2 (xstream-open-extid effective-extid)))
	     ;; 	(with-zstream (zi2 :input-stack (list xi2))
	     ;; 	  (ensure-dtd)
	     ;; 	  (p/ext-subset zi2)
	     ;; 	  (when (and fresh-dtd-p
	     ;; 		     *cache-all-dtds*
	     ;; 		     *validate*
	     ;; 		     (not (standalone-p *ctx*)))
	     ;; 	    (setf (getdtd sysid *dtd-cache*) (dtd *ctx*)))))
	     ))))
      (sax:end-dtd (handler *ctx*))
      (let ((dtd (dtd *ctx*)))
        (sax:entity-resolver
         (handler *ctx*)
         (lambda (name handler) (resolve-entity name handler dtd)))
        (sax::dtd (handler *ctx*) dtd))
      (list :DOCTYPE name extid))))

(defun read-tag-2 (zinput input kind)
  (let ((name (read-name-token input))
        (atts nil))
    (setf atts (read-attribute-list zinput input nil))
    ;; REDONE done check this
    ;; check for double attributes
    ;; (do ((q atts (cdr q)))
    ;;     ((null q))
    ;;   (cond ((find (caar q) (cdr q) :key #'car)
    ;;          (wf-error zinput "Attribute ~S has two definitions in element ~S."
    ;; 		       (rod-string (caar q))
    ;; 		       (rod-string name)))))
    (cond ((eq (peek-rune input) #/>)
           (consume-rune input)
           (values kind (cons name atts)))
          ((eq (peek-rune input) #//)
           (consume-rune input)
           (check-rune input #/> (read-rune input))
           (values :ztag (cons name atts)))
          (t
           (wf-error zinput "syntax error in read-tag-2.")) )))
