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
                                     (loop for ,idx = 0 then (1+ ,idx)
                                           for ,subtree in ,subtree-var
                                           collect (,rec ,subtree
                                                    (cons ,idx ,route-var)))
                                     ,subtree-var)))
       (labels ((,rec (,subtree-var ,route-var)
                  ,@body))
         (,rec ,tree (list 0))))))

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


(defun route-normalize (raw-route)
  (drop (reverse raw-route)))

(lambda (base subtree)
  (multiple-value-bind (retrieved detected?)
    (retrieve-by-route base (route-normalize (find-route subtree base)))
    (and (equal retrieved subtree)
         (eq detected? t))))

(defun start-with (x y)
  (and (shorter x y)
       (equal x (take y (length x)))))

(defun reserve-route (route subtree ref-mark)
  (let ((reserved t))
    (dlambda (:route () (route-normalize route))
             (:resolve () (if reserved (cons ref-mark route) subtree))
             (:cancel () (setf reserved nil)))))

(defun in-reserved-list (route reserved-list)
  (let ((route (route-normalize route)))
    (some #'(let ((reserved-route (funcall _ :route)))
              (or (start-with route reserved-route)
                  (start-with reserved-route route)))
          reserved-list)))

;;; RDIFF function returns a diff format called ``refdiff''
(defun rdiff (base modified refmark &optional (allowed-distance 0))
  (with-route (node r) (rdiff% base modified refmark allowed-distance)
    (cond ((functionp node) (funcall node :resolve))
          ((atom node) node)
          (t next-level))))

(defun rdiff% (base modified refmark allowed-distance)
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
             :pred #'(or (atom a0) (eq (car a0) refmark)))
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

(defun merge-lost (refdiff lostnode-lst refmark)
  (labels ((rec (node route)
             (let ((lostnodes (remove-if-not (p (equal (drop _ 2) route)) lostnode-lst))
                   (nodelength (length node)))
               (mapcan (lambda (order)
                         (let* ((cur-item (nth order node))
                                (cur-item-available? (or cur-item (< order nodelength))))
                           (cond ((or (atom cur-item) (%refnode-p cur-item))
                                  (let ((lost (member order lostnodes :key #'second)))
                                    (list/det
                                      (lost (car lost))
                                      (cur-item-available? cur-item))))
                                 ((member order lostnodes :key #'second)
                                  ;; the case that a node (cur-item) that is not
                                  ;; a leaf node has LOST. If such node has not
                                  ;; yet lost, then it will be recursively processed.
                                  (list/det
                                    (t (car (member order lostnodes :key #'second)))
                                    (cur-item-available? cur-item)))
                                 (t (list (rec (nth order node) (cons order route)))))))
                       (iota (max (1+ (apply #'max 0 (mapcar #'second lostnodes)) )
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
          (t (rec refdiff (list 0))))))

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
