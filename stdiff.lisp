;;;; Better diff for Lisp, the language that has available READer.
;;; This project is spun off from update-function project in order
;;; to construct a diff algorithm that is aware of wrapping operation.
;;; Not only the wrapping operation, but also insertion or extraction
;;; are targets of this project.
(in-package :stdiff)

(defun proper-list-p (obj)
  (and (listp obj) (null (cdr (last obj)))))

(defmacro with-route ((subtree-var route-var &optional (initial-route '(list 0))) tree &body body)
  (with-gensyms (rec idx subtree)
    `(symbol-macrolet ((next-level (if (proper-list-p ,subtree-var)
                                     (loop :for ,idx = 0 :then (1+ ,idx)
                                           :for ,subtree :in ,subtree-var
                                           collect (,rec ,subtree
                                                         (cons ,idx ,route-var)))
                                     ,subtree-var)))
       (labels ((,rec (,subtree-var ,route-var)
                  ,@body))
         (,rec ,tree ,initial-route)))))

(defmacro traverse/route (var-tree-pairs (route-var invalid-node &optional (style :union)) &body body)
  (with-gensyms (rec order maxorder)
    (let* ((variables (mapcar #'car var-tree-pairs))
           (sub-vars (mapcar #'(gensym (concat-str "SUB-" (string _))) variables)))
      `(let ((,invalid-node (gensym)))
         (labels ((,(intern (concat-str (symbol-name invalid-node) "-P")) (node)
                    (eq node ,invalid-node)))
           (symbol-macrolet ((next-level
                               (if (,(case style
                                       (:union 'or)
                                       (:intersection 'and)
                                       (t style))
                                     ,@(mapcar #`(proper-list-p ,a0) variables))
                                 (let ((,maxorder (max ,@(mapcar #`(length (check #'listp ,a0)) variables))))
                                   (remove ,invalid-node
                                           (loop :for ,order = 0 :then (1+ ,order)
                                                 ,@(mapcan #2`(:for ,a0 :in (fillin (check #'listp ,a1) ,maxorder ,invalid-node))
                                                           sub-vars variables)
                                                 :collect (,rec ,@sub-vars (cons ,order ,route-var))))))))
             (labels ((,rec (,@variables ,route-var)
                        ,@body))
               (,rec ,@(mapcar #'second var-tree-pairs) (list 0)))))))))

(defun find-route (subtree code)
  (let (result)
    (with-route (diff route) code
      (if (equal diff subtree)
        (push route result)
        next-level)
      result)))

(defun levenshtein-distance (str0 str1 &key (test #'eql))
  (if (not (shorter-or-equal str0 str1))
    (levenshtein-distance str1 str0)
    ;; If str1 is a list, NREVERSE is not proper here.
    (let ((reversed-str1 (reverse (coerce str1 'cons))))
      (labels ((rec (x)
                 (if x
                   (let ((predecessors (rec (cdr x))))
                     (nreverse
                       (reduce (lambda (cur-partial pred-pair)
                                 (cons (min (1+ (car cur-partial))
                                            (1+ (car pred-pair))
                                            (cdr pred-pair))
                                       cur-partial))
                               (mapcar (lambda (alphabet1 pred predpred)
                                         (cons pred
                                               (wrap-unless
                                                 (funcall test alphabet1 (car x))
                                                 (1+ (requisite predpred)))))
                                       reversed-str1
                                       (drop predecessors)
                                       predecessors)
                               :initial-value (list (length x)))))
                   (iota (1+ (length str1))))))
        (last1 (rec (coerce str0 'cons)))))))

(defun retrieve-by-route (code route)
  " The first value is the retrieved code and the second value denotes
    if a code is detected or not."
  (cond ((null route) (values code t))
        ((atom code) (values nil nil))
        ((< (maxidx code) (car route)) (values nil nil))
        (t (retrieve-by-route (nth (car route) code) (cdr route)))))

(defun maxidx (lst)
  (1- (length lst)))

(defun route-normalize (rroute)
  (drop (reverse rroute)))

(defun start-with (x y)
  (and (shorter x y)
       (equal x (take y (length x)))))

(defun start-with-or-equal (x y)
  (or (equal x y) (start-with x y)))

(defun route-booking (mark rroute subtree &optional cont (home rroute))
  (let ((valid? t) (recalculated? nil))
    (dlambda (:route () (route-normalize rroute))
             (:rroute () rroute)
             (:mark () mark)
             (:subtree () subtree)
             (:home () (route-normalize home))
             (:home-rroute () home)
             (:valid? () valid?)
             (:alive? () (or valid? recalculated?))
             (:check-in () (cond (valid?  (cons mark rroute))
                                 (recalculated? (funcall (alambda (ch)
                                                           (if (functionp ch)
                                                             (funcall ch :check-in)
                                                             (mapcar #'self ch)))
                                                         subtree))
                                 (t subtree)))
             (:cancel ()
              (setf valid? nil)
              (when cont
                (setf recalculated? t)
                (setf subtree (funcall cont)))))))

;;; The structure retuned from RAWDIFF is called ``rawdiff''.
(defun rawdiff (base modified refmark lostmark citedmark allowed-distance)
  (multiple-value-bind (modtree basebook) (rdiff% base modified refmark lostmark citedmark allowed-distance)
    (values
      (with-route (node r) modtree
        (cond ((functionp node) (if (funcall node :alive?)
                                  (funcall node :check-in)
                                  'dead))
              ((atom node) node)
              (t next-level)))
      (construct-losttree base basebook))))

(defun find-ref-candidates (tree rroute allowed-distance base)
  (some #'(and (<= (levenshtein-distance rroute a0) allowed-distance) a0)
        (find-route tree base)))

(defun collect-ref-candidates (tree rroute allowed-distance base)
  (remove-if-not #'(and (<= (levenshtein-distance rroute a0)
                            allowed-distance)
                        a0)
                 (find-route tree base)))

(defun route-relation (x y)
  " Check if the route X is included in the route Y. The returned value
   talks about X. If X is included in Y then :INDIRECT is returned. If X
   includes Y then :PARTLY is included. :DIRECT is returned if X and Y
   are equal. It returns NIL if there is no relation between X and Y."
  (cond ((equal x y) :direct)
        ((start-with y x) :indirect)
        ((start-with x y) :partly)))

(defun collect-partly-bookings (route book)
  (remove-if-not #'(and (funcall a0 :valid?)
                        (start-with route (funcall a0 :home)))
                 book))

(defun check-booking (rroute basebook)
  (let ((route (route-normalize rroute)))
    (acond ((find-if #'(and (funcall a0 :valid?)
                            (start-with-or-equal (funcall a0 :home) route))
                     basebook)
            (values it
                    (route-relation route (funcall it :home))
                    (funcall it :mark)))
           ((collect-partly-bookings route basebook)
            (values it :partly t))
           (t (values nil nil nil)))))

(defun rdiff% (base modified refmark lostmark citedmark allowed-distance)
  (let (basebook modbook)
    (labels ((booking-as-ref (cited node cont cur)
               (multiple-value-bind (booking relation mark)
                 (check-booking cited basebook)
                 (if booking
                   (case relation
                     (:partly
                       (mapc #'(funcall _ :cancel) booking)
                       (mapc #'(funcall _ :cancel) (collect-partly-bookings
                                                     (route-normalize cited) modbook))
                       (stack-ref-booking cited node cont cur))
                     (:direct (cond ((eq mark lostmark)
                                     (funcall booking :cancel)
                                     (stack-ref-booking cited node cont cur))
                                    ((eq mark citedmark) (funcall cont))))
                     (:indirect (cond ((eq mark lostmark)
                                       (funcall booking :cancel)
                                       (let ((croute (route-normalize cited)))
                                         (with-route (subnode subrroute (funcall booking :rroute)) (funcall booking :subtree)
                                           (case (route-relation croute (route-normalize subrroute))
                                             (:direct (push (route-booking citedmark cur subnode nil subrroute) basebook))
                                             (:indirect next-level)
                                             (t (push (route-booking lostmark subrroute subnode) basebook)))))
                                       (car (push (route-booking refmark cited node cont) modbook)))
                                      ((eq mark citedmark) (funcall cont)))))
                   (stack-ref-booking cited node cont cur))))
             (booking-as-lost (rroute node)
               (multiple-value-bind (booking relation)
                 (check-booking rroute basebook)
                 (if booking
                   (case relation
                     ((:direct :indirect) nil)
                     (:partly (with-route (subnode subrroute rroute) node
                                (multiple-value-bind (booking2 relation2)
                                  (check-booking subrroute booking)
                                  (declare (ignore booking2))
                                  (case relation2
                                    (:direct nil)
                                    (:partly next-level)
                                    ((nil) (push (route-booking lostmark subrroute subnode) basebook)))))))
                   (push (route-booking lostmark rroute node) basebook))))
             (stack-ref-booking (cited node cont cur)
               (push (route-booking citedmark cur node nil cited) basebook)
               (car (push (route-booking refmark cited node cont) modbook))))
      (symbol-macrolet ((cont (lambda () (if (proper-list-p mnode)
                                           next-level
                                           (lambda (_) (declare (ignore _)) mnode)))))
        (values
          (traverse/route ((bnode base) (mnode modified)) (rroute invalid)
            (cond ((and (not (invalid-p mnode)) (not (invalid-p bnode)))
                   (acond ((equal mnode bnode)
                           (booking-as-ref rroute bnode cont rroute))
                          ((find-ref-candidates mnode rroute allowed-distance base)
                           (booking-as-lost rroute bnode)
                           (booking-as-ref it mnode cont rroute))
                          ((and (not (proper-list-p bnode)) (not (proper-list-p mnode)))
                           (booking-as-lost rroute bnode)
                           mnode)
                          ((not (proper-list-p bnode))
                           (booking-as-lost rroute bnode)
                           next-level)
                          ((not (proper-list-p mnode))
                           (booking-as-lost rroute bnode)
                           mnode)
                          (t next-level)))
                  ((invalid-p bnode)
                   (acond ((find-ref-candidates mnode rroute allowed-distance base)
                           (booking-as-ref it mnode cont rroute))
                          ((proper-list-p mnode) next-level)
                          (t mnode)))
                  ((invalid-p mnode)
                   (booking-as-lost rroute bnode)
                   invalid)))
          (remove-if-not #'(funcall _ :alive?) basebook))))))

(defun construct-losttree (base basebook)
  (with-route (node rroute) base
    (aif (member rroute basebook :key #'(funcall _ :home-rroute) :test #'equal)
      (funcall (car it) :check-in)
      next-level)))

(defun refnode-p (node refmark)
  (and (proper-list-p node) (eq (car node) refmark)))

(defun lostnode-p (node lostmark)
  (and (proper-list-p node) (eq (car node) lostmark)))

;;; The structure returned from DIFF is called ``diff.''
;;; The contents is identical to rawdiff for now.
(defun diff (base modified &optional (refmark (gensym "REF"))
                 (lostmark (gensym "LOST")) (allowed-distance 0))
  (values
    (rawdiff base modified refmark lostmark allowed-distance)
    refmark
    lostmark))

;;; A converter is a 3 parameter function. It takes node, route, and
;;; codelet. A converter should return a codelet
;;; Currently, node and codelet are completely same for new nodes
;;; because there is no special format for new node in diff. In order to
;;; achieve a suite a certain consistensy, it is good to introduce a
;;; special data structure for new node, too.  Moreover, nodes can
;;; be expressed as a class.
(defun apply-converters (diff base refmark lostmark newnode-converter lostnode-converter refnode-converter)
  (with-route (cur route) diff
    (cond ((refnode-p cur refmark)
           (funcall refnode-converter cur route
                    (retrieve-by-route base (route-normalize (drop cur)))))
          ((lostnode-p cur lostmark)
           (funcall lostnode-converter cur route
                    (retrieve-by-route base (route-normalize (drop cur)))))
          ((newnode-p cur refmark lostmark)
           (funcall newnode-converter cur route cur))
          (t next-level))))

;;; An easy-converter takes a codelet as its only argument.
(defun apply-modifiednode-converters
  (diff base refmark lostmark newnode-easy-converter lostnode-easy-converter)
  (macrolet ((gen-convereter (easy-converter)
               `(lambda (node route codelet)
                  (declare (ignore node route))
                  (funcall ,easy-converter codelet))))
    (apply-converters
      diff base refmark lostmark
      (gen-convereter newnode-easy-converter)
      (gen-convereter lostnode-easy-converter)
      (gen-convereter #'identity))))

(defun newnode-p (node refmark lostmark)
  (or (atom node) (composed-of-newnodes-p node refmark lostmark)))

(defun composed-of-newnodes-p (tree refmark lostmark)
  (reduce (lambda (acc node)
            (and acc
                 (cond ((atom node) t)
                       ((or (refnode-p node refmark) (lostnode-p node lostmark)) nil)
                       (t (composed-of-newnodes-p node refmark lostmark)))))
          tree
          :initial-value t))
