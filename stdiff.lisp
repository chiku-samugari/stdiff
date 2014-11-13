;;;; Better diff for Lisp, the language that has available READer.
;;; This project is spun off from update-function project in order
;;; to construct a diff algorithm that is aware of wrapping operation.
;;; Not only the wrapping operation, but also insertion or extraction
;;; are targets of this project.
(in-package :stdiff)

(defun proper-list-p (obj)
  (and (listp obj) (null (cdr (last obj)))))

(defmacro with-route ((subtree-var route-var) tree &body body)
  (with-gensyms (rec idx subtree)
    `(symbol-macrolet ((next-level (if (proper-list-p ,subtree-var)
                                     (loop :for ,idx = 0 :then (1+ ,idx)
                                           :for ,subtree :in ,subtree-var
                                           collect (,rec ,subtree
                                                    (cons ,idx ,route-var)))
                                     ,subtree-var)))
       (labels ((,rec (,subtree-var ,route-var)
                  ,@body))
         (,rec ,tree (list 0))))))

(defmacro traverse/route (var-tree-pairs route-var invalid-p-name style &body body)
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
                                         :collect (,rec ,@sub-vars (cons ,order ,route-var)))))))
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

;; TODO: subtree is not used at all.
(defun reserve-route (rroute found-rroute subtree mark)
  (let ((reserved t))
    (dlambda (:route () (route-normalize rroute))
             (:resolve () (if reserved (cons mark rroute) subtree))
             (:found-rroute () found-rroute)
             (:cancel () (setf reserved nil)))))

(defun in-reserved-list (rroute reserved-list)
  (let ((route (route-normalize rroute)))
    (some #'(let ((reserved-route (funcall _ :route)))
              (or (start-with route reserved-route)
                  (start-with reserved-route route)))
          reserved-list)))

;;; RDIFF function returns a diff format called ``refdiff''
(defun rdiff (base modified refmark allowed-distance)
  (with-route (node r) (rdiff% base modified refmark :came-from allowed-distance)
    (cond ((functionp node) (funcall node :resolve))
          ((atom node) node)
          (t next-level))))

(defun rdiff% (base modified refmark camemark allowed-distance)
  ;; TODO: The word ``reserve'' is no more proper, I feel. Almost all
  ;; nodes are registered into the list and referred during the
  ;; construction of ``refdiff''. Therefore, I feel ``book'' is more
  ;; properer.
  (let (reserved-routes)
    (labels ((reserve (route found node mark)
               ;; TODO: What should happen if a LOST reserved node or a
               ;; child of such node is later tried to be reserved?
               ;; TODO: What should happen if some of children of the
               ;; booking node is reserved as LOST?
               ;; TODO: What should happen if a larger reservation is
               ;; already established?
               (aand (smaller-reservations route)
                     (mapc #'(funcall _ :cancel) it))
               (aand (booked-as-lost route)
                     )
               (car (push (reserve-route route found node mark) reserved-routes)))
             (smaller-reservations (route)
               (remove-if-not #'(start-with (route-normalize route) (funcall _ :route))
                              reserved-routes)))
      (traverse/route ((bnode base) (mnode modified)) route invalid-p :union
        (cond ((and (not (invalid-p mnode)) (not (invalid-p bnode)))
               (acond ((equal mnode bnode) (reserve route route bnode refmark))
                      ((some #'(and (<= (levenshtein-distance route a0) allowed-distance) a0)
                             (find-route mnode base))
                       (reserve it route mnode camemark))
                      (t next-level)))
              ((invalid-p bnode) mnode)
              ((invalid-p mnode)
               (aif (find-if #'(equal (funcall _ :route) (route-normalize route)) reserved-routes)
                 (car (push (reserve-route  (funcall it :found-rroute) route bnode :wentto) reserved-routes))
                 (reserve route route bnode :lost))))))))

#+nil(defun rdiff% (base modified refmark allowed-distance)
  (let (reserved-routes)
    (with-route (cur route) modified
      (acond ((multiple-value-bind (code detected)
                (retrieve-by-route base (route-normalize route))
                (and detected (equal cur code)))
              (acond ((not (in-reserved-list route reserved-routes))
                      (car (push (reserve-route route cur refmark) reserved-routes)))
                     ((remove-if-not #'(start-with (route-normalize route) (funcall _ :route))
                                     reserved-routes)
                      (progn (mapc #'(funcall _ :cancel) it)
                             (car (push (reserve-route route cur refmark) reserved-routes))))
                     (t next-level)))
             ((some #'(if (<= (levenshtein-distance route a0)
                              allowed-distance)
                        a0)
                    (find-route cur base))
              (let ((route it))
                (acond ((not (in-reserved-list route reserved-routes))
                        (car (push (reserve-route route cur refmark) reserved-routes)))
                       ((remove-if-not #'(start-with (route-normalize route) (funcall _ :route)) reserved-routes)
                        (progn (mapc #'(funcall _ :cancel) it)
                               (car (push (reserve-route route cur refmark) reserved-routes))))
                       (t next-level))))
             (t next-level)))))

(defun refnode-list (refdiff refmark)
  (let (result)
    (maptree #'(unless (atom a0)
                 (car (push (cdr a0) result)))
             refdiff
             :pred #'(or (atom a0) (refnode-p a0 refmark)))
    result))

(defun lostnode-list (refdiff base refmark lostmark)
  (let ((refnodes (refnode-list refdiff refmark))
        result)
    (with-route (sub route) base
      (cond ((find route refnodes :test #'equal)) ; do nothing
            ((find-if #'(start-with (route-normalize route) (route-normalize _))
                      refnodes)
             next-level)
            (t (push (cons lostmark route) result))))
    (nreverse result)))

;; rroute denotes ``raw-route''
(defun rroute<-node (node)
  (drop node))

;; nroute denotes ``normalized route''
(defun nroute<-node (node)
  (route-normalize (rroute<-node node)))

(defun merge-lost (refdiff lostnode-lst refmark)
  (macrolet ((stackprint (fstr depth &body body)
               `(format t ,(concat-str "~{~T~T~*~}" fstr) (iota ,depth) ,@body)))
    (labels ((rec (node route)
               (let* ((near-lostnodes (remove-if-not (p (equal (drop (rroute<-node _)) route)) lostnode-lst))
                      (lost-kindreds (remove-if-not #'(start-with (route-normalize route)
                                                                  (nroute<-node _))
                                                    lostnode-lst))
                      (far-lostnodes (set-difference lost-kindreds near-lostnodes :test #'equal))
                      (nodelength (length node))
                      (depth (length (route-normalize route))))
                 (format t "~&")
                 (stackprint "ROUTE ~A [cf. depth = ~D]~%" depth route depth)
                 ;(format t "~&~{~T~*~}ROUTE ~A [cf. depth = ~D]~%" (iota depth) route depth)
                 ;(format t "NEAR LOSTNODES: ~A~%" near-lostnodes)
                 ;(format t "LOST KINDREDS ~A~%" lost-kindreds)
                 ;(format t "FAR LOSTNODES ~A~%" far-lostnodes)
                 (mapcan (lambda (order)
                           (stackprint  "Processing ~A~%" depth (cons order route))
                           (let* ((cur-item (nth order node))
                                  (cur-item-available? (< order nodelength))
                                  (orphans (remove-if-not #'(eql (nth depth (nroute<-node _)) order)
                                                          far-lostnodes)))
                             (and orphans (stackprint "ORPHANS: ~A~%" depth (mapcar #'(retrieve-by-route *base* (nroute<-node _)) orphans)))
                             (cond ((or (atom cur-item) (%refnode-p cur-item))
                                    (let ((lost (member order near-lostnodes :key #'second)))
                                      (if lost
                                        (stackprint "LOST: ~A, " depth
                                                    (retrieve-by-route *base* (nroute<-node (car lost))))
                                        (stackprint "" depth))
                                      (format t "CUR-ITEM: ~A [~:[NEW~;REF~] ~A]~%"
                                              (if (atom cur-item) cur-item (retrieve-by-route *base* (nroute<-node cur-item)))
                                              (%refnode-p cur-item) cur-item)
                                      (list/det
                                        (lost (car lost))
                                        (orphans (rec nil (cons order route)))
                                        (cur-item-available? cur-item))))
                                   ((member order near-lostnodes :key #'second)
                                    ;; Node is lost but not replaced by a
                                    ;; new node.
                                    (list/det
                                      (t (car (member order near-lostnodes :key #'second)))
                                      (cur-item-available? cur-item)))
                                   #+nil((and (not cur-item-available?) orphans)
                                         (rec nil (cons order route)))
                                   (t (list (rec (if (atom cur-item)
                                                   nil ; in order to process orphans.
                                                   cur-item)
                                                 (cons order route)))))))
                         (iota (max (1+ (apply #'max 0 (mapcar #'(nth depth (nroute<-node _)) lost-kindreds)))
                                    nodelength
                                    (1+ (apply #'max 0 (filter (lambda (child)
                                                                 (and (%refnode-p child)
                                                                      (second child)))
                                                               node))))))))
             (%refnode-p (node) (refnode-p node refmark)))
      (cond ((or (atom refdiff) (%refnode-p refdiff))
              (if (eql 0 (second (car lostnode-lst)))
                (list (car lostnode-lst) refdiff)
                refdiff))
            ((member '(0) lostnode-lst :key #'drop :test #'equal)
             (list (car (member '(0) lostnode-lst :key #'drop :test #'equal)) refdiff))
            (t (rec refdiff (list 0)))))))

(defun refnode-p (node refmark)
  (and (proper-list-p node) (eq (car node) refmark)))

(defun lostnode-p (node lostmark)
  (and (proper-list-p node) (eq (car node) lostmark)))

;;; The structure retuned from RAWDIFF is called ``rawdiff''.
(defun rawdiff (base modified refmark lostmark &optional (allowed-distance 0))
  (let ((refdiff (rdiff base modified refmark allowed-distance)))
    (merge-lost refdiff
                (lostnode-list refdiff base refmark lostmark)
                refmark)))

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
