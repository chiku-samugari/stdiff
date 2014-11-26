;;;; Better diff for Lisp, the language that has available READer.
;;; This project is spun off from update-function project in order
;;; to construct a diff algorithm that is aware of wrapping operation.
;;; Not only the wrapping operation, but also insertion or extraction
;;; are targets of this project.
(in-package :stdiff)

(defun proper-list-p (obj)
  (and (consp obj) (null (cdr (last obj)))))

(defmacro with-route ((subtree-var route-var &optional (initial-route '(list 0))) tree &body body)
  (with-gensyms (rec idx subtree)
    `(symbol-macrolet ((next-level (if (proper-list-p ,subtree-var)
                                     (loop :for ,idx = 0 :then (1+ ,idx)
                                           :for ,subtree :in ,subtree-var
                                           :collect (,rec ,subtree
                                                         (cons ,idx ,route-var)))
                                     ,subtree-var)))
       (labels ((,rec (,subtree-var ,route-var)
                  ,@body))
         (,rec ,tree ,initial-route)))))

(defmacro traverse/route (var-tree-pairs (route-var invalid-p-name &optional (style :union)) &body body)
  (with-gensyms (rec order maxorder invalid-node)
    (let* ((variables (mapcar #'car var-tree-pairs))
           (sub-vars (mapcar #'(gensym (concat-str "SUB-" (string _))) variables)))
      `(let ((,invalid-node (gensym)))
         (labels ((,invalid-p-name (node)
                    (eq node ,invalid-node)))
           (symbol-macrolet ((next-level
                               (if (,(case style
                                       (:union 'or)
                                       (:intersection 'and)
                                       (t style))
                                     ,@(mapcar #`(proper-list-p ,a0) variables))
                                 (let ((,maxorder (max ,@(mapcar #`(length (check #'listp ,a0)) variables))))
                                   (loop :for ,order = 0 :then (1+ ,order)
                                         ,@(mapcan #2`(:for ,a0 :in (fillin (check #'listp ,a1) ,maxorder ,invalid-node))
                                                   sub-vars variables)
                                         :do (,rec ,@sub-vars (cons ,order ,route-var)))))))
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
  (let ((valid? t))
    (dlambda (:route () (route-normalize rroute))
             (:rroute () rroute)
             (:mark () mark)
             (:subtree () subtree)
             (:home () (route-normalize home))
             (:home-rroute () home)
             (:valid? () valid?)
             (:check-in () (cons mark rroute))
             (:cancel ()
              (setf valid? nil)
              (when cont
                (funcall cont))))))

;;; The structure retuned from RAWDIFF is called ``rawdiff''.
(export
  (defun rawdiff (base modified allowed-distance newmark refmark lostmark citedmark)
    (multiple-value-bind (modbook basebook)
      (rdiff% base modified allowed-distance newmark refmark lostmark citedmark)
      (values
        (rawdiff<-book modified modbook)
        (rawdiff<-book base basebook)))))

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

(defun collect-partly-bookings (route book fieldspec)
  (remove-if-not #'(and (funcall a0 :valid?)
                        (start-with route (funcall a0 fieldspec)))
                 book))

(defun check-booking (rroute basebook)
  (let ((route (route-normalize rroute)))
    (acond ((find-if #'(and (funcall a0 :valid?)
                            (start-with-or-equal (funcall a0 :home) route))
                     basebook)
            (values it
                    (route-relation route (funcall it :home))
                    (funcall it :mark)))
           ((collect-partly-bookings route basebook :home)
            (values it :partly t))
           (t (values nil nil nil)))))

(defun rdiff% (base modified allowed-distance newmark refmark lostmark citedmark)
  (let (basebook modbook)
    (labels ((booking-as-ref (cited node cont cur)
               (multiple-value-bind (booking relation mark)
                 (check-booking cited basebook)
                 (if booking
                   (case relation
                     (:partly
                       (mapc #'(funcall _ :cancel) booking)
                       (mapc #'(funcall _ :cancel)
                             (collect-partly-bookings
                               (route-normalize cited) (remove-if-not #'(eq (funcall _ :mark) refmark) modbook) :route))
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
                                       (push (route-booking refmark cited node cont cur) modbook))
                                      ((eq mark citedmark) (funcall cont)))))
                   (stack-ref-booking cited node cont cur))))
             (booking-as-new (rroute node)
               (push (route-booking newmark rroute node) modbook))
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
               (push (route-booking refmark cited node cont cur) modbook)))
      (symbol-macrolet ((cont (lambda () (if (proper-list-p mnode)
                                           next-level
                                           (booking-as-new rroute mnode)))))
        (traverse/route ((bnode base) (mnode modified)) (rroute invalid-p)
          (cond ((and (not (invalid-p mnode)) (not (invalid-p bnode)))
                 (acond ((equal mnode bnode)
                         (booking-as-ref rroute bnode cont rroute))
                        ((find-ref-candidates mnode rroute allowed-distance base)
                         (booking-as-lost rroute bnode)
                         (booking-as-ref it mnode cont rroute))
                        ((and (not (proper-list-p bnode)) (not (proper-list-p mnode)))
                         (booking-as-lost rroute bnode)
                         (booking-as-new rroute mnode))
                        ((not (proper-list-p bnode))
                         (booking-as-lost rroute bnode)
                         next-level)
                        ((not (proper-list-p mnode))
                         (booking-as-lost rroute bnode)
                         (booking-as-new rroute mnode))
                        (t next-level)))
                ((invalid-p bnode)
                 (acond ((find-ref-candidates mnode rroute allowed-distance base)
                         (booking-as-ref it mnode cont rroute))
                        ((proper-list-p mnode) next-level)
                        (t (booking-as-new rroute mnode))))
                ((invalid-p mnode) (booking-as-lost rroute bnode))))
        (values
          (remove-if-not #'(funcall _ :valid?) modbook)
          (remove-if-not #'(funcall _ :valid?) basebook))))))

(defun rawdiff<-book (code book)
  (with-route (node rroute) code
    (or (car (member rroute book :key #'(funcall _ :home-rroute) :test #'equal))
        next-level)))

(defun newnode-p (node newmark)
  (and (proper-list-p node) (eq (car node) newmark)))

(defun refnode-p (node refmark)
  (and (proper-list-p node) (eq (car node) refmark)))

(defun lostnode-p (node lostmark)
  (and (proper-list-p node) (eq (car node) lostmark)))

(defun citednode-p (node citedmark)
  (and (proper-list-p node) (eq (car node) citedmark)))

;;; The structure returned from DIFF is called ``diff.''
(defun diff (base modified allowed-distance
                    &optional (newmark (gensym "NEW"))
                    (refmark (gensym "REF"))
                    (lostmark (gensym "LOST"))
                    (citedmark (gensym "CITED")))
  (multiple-value-call #'(values (retrieve-from-rawdiff a0)
                                 (retrieve-from-rawdiff a1)
                                 newmark refmark lostmark citedmark)
    (rawdiff base modified allowed-distance newmark refmark lostmark citedmark)))

(defun retrieve-from-rawdiff (rawdiff)
  (with-route (node rr) rawdiff
    (if (functionp node)
      (funcall node :check-in)
      next-level)))

;;; A converter is a 3 parameter function. It takes node, route, and
;;; codelet. A converter should return a codelet
;;; Currently, node and codelet are completely same for new nodes
;;; because there is no special format for new node in diff. In order to
;;; achieve a suite a certain consistensy, it is good to introduce a
;;; special data structure for new node, too.  Moreover, nodes can
;;; be expressed as a class.
(defun apply-converters (base modified reftree losttree
                              newmark refmark lostmark citedmark
                              newnode-converter refnode-converter
                              lostnode-converter citednode-converter)
  (values
    (with-route (node rroute) reftree
      (cond ((refnode-p node refmark)
             (funcall refnode-converter node rroute
                      (retrieve-by-route base (nroute<-node node))))
            ((newnode-p node newmark)
             (funcall newnode-converter node rroute
                      (retrieve-by-route modified (nroute<-node node))))
            (t next-level)))
    (with-route (node rroute) losttree
      (cond ((lostnode-p node lostmark)
             (funcall lostnode-converter node rroute
                      (retrieve-by-route base (nroute<-node node))))
            ((citednode-p node citedmark)
             (funcall citednode-converter node rroute
                      (retrieve-by-route base (nroute<-node node))))
            (t next-level)))))

(defun nroute<-node (node)
  (route-normalize (drop node)))

;;; An easy-converter takes a codelet as its only argument.
(export
  (defun apply-easy-converters
    (base modified reftree losttree newmark refmark lostmark citedmark
          newnode-easy-converter refnode-easy-converter
          lostnode-easy-converter citednode-easy-converter)
    (macrolet ((gen-convereter (easy-converter)
                 `(lambda (node route codelet)
                    (declare (ignore node route))
                    (funcall ,easy-converter codelet))))
      (apply-converters
        base modified reftree losttree newmark
        refmark lostmark citedmark
        (gen-convereter newnode-easy-converter)
        (gen-convereter refnode-easy-converter)
        (gen-convereter lostnode-easy-converter)
        (gen-convereter citednode-easy-converter)))))
