;;;; Better diff for Lisp, the language that has available READer.
;;; This project is spun off from update-function project in order
;;; to construct a diff algorithm that is aware of wrapping operation.
;;; Not only the wrapping operation, but also insertion or extraction
;;; is also targets of this project.
(load "packages.lisp")

(in-package :chiku.diff)

;;; Each component of result list is a dot pair whose CAR is route and
;;; CDR is code.
;;; Please be aware that this function name is conflicting in my original
;;; library called chat-with-tree.
(defun collect-subtree (tree depth)
  (labels ((rec (tree depth route)
             (if (and (< 0 depth) (proper-list-p tree))
               (loop for idx = 0 then (1+ idx)
                     for subtree in tree
                     append (cons (list (cons idx route) subtree)
                                  (rec subtree (1- depth) (cons idx route)))))))
    (cons (list (list 0) tree) (rec tree depth (list 0)))))

(defun proper-list-p (obj)
  (and (listp obj) (null (cdr (last obj)))))

(collect-subtree *first-impl* 3)
(collect-subtree *first-impl* 4)
(collect-subtree *first-impl* 5)
(collect-subtree *first-impl* 6)

(dolist (ref (collect-subtree *first-impl* 3))
  (destructuring-bind (route subtree) ref
    (format t "~a : ~a~%" (reverse route) subtree)))

;;; DEPTH should be determined with a reasonable criteria.
(defun collect-effective-refs (code)
  (let ((counter (get-counter)))
    (filter (lambda (subtree)
              (and (not (atom subtree))
                   (< 2 (length (flatten subtree)))
                   (cons (funcall counter) subtree)))
            (collect-subtree code 10))))

(defun get-counter (&optional (start 0))
  (let ((c (1- start)))
    (lambda () (incf c))))

(collect-effective-refs *first-impl*)

(collect-subtree *first-impl* 2)

(collect-effective-refs *first-impl*)

(let ((ref '(ref . 5))
      (route '(3 3 0))
      (base *first-impl*))
  (printing-let ((route-in-base (second (find (cdr ref) (collect-effective-refs base) :key #'car))))
    route-in-base
    (equal (drop route) route-in-base)))

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

(find-route '(nreverse lst) *first-impl*)
(find-route 'lst *first-impl*)

(defun rdiff (base modified refmark)
  (let ((subtrees (collect-effective-refs base)))
    (labels ((rec (code)
               (aif (find code subtrees :key #'last1 :test #'equal)
                 (cons refmark (car it))
                 (if (atom code) code
                   (mapcar #'rec code)))))
      (rec modified))))

(rdiff *first-impl* *second-impl* 'ref)
(rdiff *first-impl* *first-impl* 'ref)
(rdiff '(a (x y z) b c) '(print (a (x y z) b c)) 'ref)
(rdiff '(a (x y z) b c) '(a (x s z) b c) 'ref)

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

(levenshtein-distance '(1) '(1))
(levenshtein-distance '(1 2 3) '(1 2 4))
(levenshtein-distance '(1 1 2 2 3 0) '(1 2 2 3 0) :test #'equal)
(levenshtein-distance (coerce "kitten" 'cons) (coerce "akitten" 'cons))
(levenshtein-distance (coerce "kitten" 'cons) (coerce "sitting" 'cons))
(levenshtein-distance (coerce "sitting" 'cons) (coerce "kitten" 'cons))
(levenshtein-distance '(a b c) '(x y z))
(levenshtein-distance '(a b c) '(a (x y z) c))

(defun retrieve-by-route (code route)
  " The first value is the retrieved code and the second value denotes
    if a code is detected or not."
  (cond ((null code) (values nil nil))
        ((null route) (values code t))
        ((atom code) (if (equal '(0) route)
                       (values code t)
                       (values nil nil)))
        (t (values (retrieve-by-route (nth (car route) code) (cdr route)) t))))

(retrieve-by-route '(a b (x (s t u) y z) c) '(2 1))

(retrieve-by-route '(a b (x (s t u) y z) c) '(2 1 2 1))

(let ((route (car (find-route '(PUSH I LST) *first-impl*))))
  (rdiff *first-impl* (retrieve-by-route *first-impl* (drop (reverse route))) 'ref))

(car (find-route '(ref . 11) (rdiff *first-impl* *second-impl* 'ref)))

(levenshtein-distance
  (mapcar (papply (rdiff *first-impl* _ 'ref))
          (retrieve-by-route *first-impl* (drop (nreverse '(2 2 3 0)))))
  (retrieve-by-route (rdiff *first-impl* *second-impl* 'ref) (drop (nreverse '(2 2 3 0))))
  :test #'equal)

(defun longer-length (sec0 sec1)
  (length (if (shorter sec0 sec1) sec1 sec0)))

(defun similar? (code0 code1)
  (< (/ (levenshtein-distance code0 code1 :test #'equal)
        (longer-length code0 code1))
     0.5))

(similar?
  (mapcar (papply (rdiff *first-impl* _ 'ref))
          (retrieve-by-route *first-impl* (drop (nreverse '(2 2 3 0)))))
  (retrieve-by-route (rdiff *first-impl* *second-impl* 'ref) (drop (nreverse '(2 2 3 0)))))

(defun white (x)
  (format t "<font color=\"#ffffff\">~%<pre> ~a</pre>~%</font>" x))

(defun red (x)
  (format t "<font color=\"#ff0000\">~%<pre> ~a</pre>~%</font>" x))

(defun green (x)
  (format t "<font color=\"#00ff00\">~%<pre> ~a</pre>~%</font>" x))

(defun showdiff (base modified distance)
    (with-route (sub route) (rdiff base modified 'ref)
      (if (or (find route
                    (find-route (retrieve-by-route modified (drop (reverse route)))
                                base)
                    :test #'equal)
              (some (papply (<= (levenshtein-distance route _) distance))
                    (find-route (retrieve-by-route modified (drop (reverse route))) base)))
        (white (retrieve-by-route modified (drop (reverse route))))
        (if (proper-list-p sub)
          (progn
            (white "(") next-level (white ")"))
          (if (consp sub)
            (green (third (find (cdr sub) (collect-effective-refs base) :key #'car)))
            (green sub))))))

(with-open-file (out "tmp.html" :direction :output :if-does-not-exist :create :if-exists :supersede)
  (let ((*standard-output* out))
    (write-line "<html> <head><title></title></head> <body bgcolor=\"000000\"><p>")
    (showdiff *first-impl* *first-impl* 0)
    (write-line "<br/>")
    (mapc (lambda (x)
            (white (format nil "~a : " x))
            (showdiff *first-impl* `(progn ,*third-impl*) x)
            (write-line "<br/>"))
          (iota 8))
    (write-line "</p></body></html>")))

(with-open-file (out "tmp.html" :direction :output :if-does-not-exist :create :if-exists :supersede)
  (let ((*standard-output* out))
    (write-line "<html> <head><title></title></head> <body bgcolor=\"000000\"><p>")
    (mapc (lambda (n)
            (white (format nil "~a : " n))
            (showdiff
              '(lambda (x)
                 (showdiff *first-impl* *second-impl* x)
                 (write-line "br/>"))
              '(lambda (x)
                 (princ x)
                 (showdiff *first-impl* *second-impl* x)
                 (write-line "br/>"))
              n)
            (write-line "<br/>"))
          (iota 4))
    (write-line "</p></body></html>")))

(defun route-normalize (raw-route)
  (drop (reverse raw-route)))

(defun start-with (x y)
  (and (shorter x y)
       (equal x (take y (length x)))))

(start-with '(0 1 2) '(0 1 2 3))
(start-with '(0 1 2) '(1 1 2 3))
(start-with '(1 1 2) '(0 1 2 3))

(defun reserve-route (route subtree ref-mark)
  (let ((reserved t))
    (dlambda (:route () (route-normalize route))
             (:resolve () (if reserved (cons ref-mark route) subtree))
             (:cancel () (setf reserved nil)))))

(defun rdiff (base modified refmark &optional allowed-distance)
  (with-route (node r)
              (let (tmp)
                (with-route (cur route) modified
                  (acond ((multiple-value-bind (code detected)
                            (retrieve-by-route base (route-normalize route))
                            (and detected (equal cur code)))
                          (acond ((and (notany #'(start-with (route-normalize route) (funcall _ :route)) tmp)
                                       (notany #'(start-with (funcall _ :route) (route-normalize route)) tmp))
                                  (car (push (reserve-route route cur refmark) tmp)))
                                 ((remove-if-not #'(start-with (route-normalize route) (funcall _ :route))
                                                 tmp)
                                  (progn (mapc #'(funcall _ :cancel) it)
                                         (car (push (reserve-route route cur refmark) tmp))))
                                 (t next-level)))
                         ((some (lambda (x)
                                  (if (<= (levenshtein-distance route x) allowed-distance)
                                    x))
                                (find-route cur base))
                          (let ((route it))
                            (acond ((and (notany #'(start-with (route-normalize route) (funcall _ :route)) tmp)
                                         (notany #'(start-with (funcall _ :route) (route-normalize route)) tmp))
                                    (car (push (reserve-route route cur refmark) tmp)))
                                   ((remove-if-not #'(start-with (route-normalize route) (funcall _ :route)) tmp)
                                    (progn (mapc #'(funcall _ :cancel) it)
                                           (car (push (reserve-route route cur refmark) tmp))))
                                   (t next-level))))
                         (t next-level))))
              (cond ((functionp node) (funcall node :resolve))
                    ((atom node) node)
                    (t next-level))))

(let* ((base '(lambda (x)
                (showdiff *first-impl* *second-impl* x)
                (write-line "br/>")))
       (modified '(lambda (x)
                    (princ x)
                    (print (showdiff *first-impl* *second-impl* x)))))
  (rdiff base modified 'ref 2))

(defun construct-routeref-lst (routeref-diff refmark)
  (let ((result))
    (maptree (lambda (leaf)
               ;; Here, we need to coerce ATOMs into NIL. The MAPTREE
               ;; implementation showed in ``Let over Lambda'' avoids
               ;; this point by throwing away the ability to recognize
               ;; S-expressions other than ATOMs as leaves.
               (if (not (atom leaf))
                 (car (push (cdr leaf) result))))
             routeref-diff
             :pred (lambda (x) (or (atom x) (eq (car x) refmark))))
    result))

(defun lost-subtree-list (routeref-diff base refmark lostmark)
  (let ((routeref-lst (construct-routeref-lst routeref-diff refmark))
        result)
    (with-route (sub route) base
      (cond ((find route routeref-lst :test #'equal) (cons refmark route))
            ((find-if (papply (start-with (route-normalize route)
                                          (route-normalize _)))
                      routeref-lst)
             next-level)
            (t (push (cons lostmark route) result))))
      (nreverse result)))

(printing-let* ((base '(lambda (x)
                         (showdiff *first-impl* *second-impl* x)
                         (write-line "br/>")))
                (modified '(lambda (x)
                             (princ x)
                             (print (showdiff *first-impl* *second-impl* x)))))
  (rdiff base modified 'ref 1)
  (lost-subtree-list (rdiff base modified 'ref 1) base 'ref 'lost))

(defun merge-lost (routeref-diff lost-subtrees refmark)
  (labels ((rec (node route)
             (if (atom node) node
               (let ((lostnodes (remove-if-not (papply (equal (drop _ 2) route)) lost-subtrees)))
                    (mapcan (lambda (order)
                              (let ((cur-item (nth order node)))
                                (cond ((member order (remove-if-not #'%refnode-p node) :key #'second)
                                       (aif (member order lostnodes :key #'second)
                                         (list (car (member order (remove-if-not #'%refnode-p node) :key #'second))
                                               (car it))
                                         (list (car (member order (remove-if-not #'%refnode-p node) :key #'second)))))
                                      ((member order lostnodes :key #'second)
                                       (if (or (and (%refnode-p cur-item ) (eql (second cur-item) order))
                                               (and (not (%refnode-p cur-item )) cur-item))
                                         (list cur-item (car (member order lostnodes :key #'second)))
                                         (list (car (member order lostnodes :key #'second)))))
                                      (t (list (rec (nth order node) (cons order route)))))))
                            (iota (max (1+ (apply #'max 0 (mapcar #'second lostnodes)) )
                                       (length node)
                                       (1+ (apply #'max 0 (filter (lambda (child) (and (%refnode-p child)
                                                                                       (second child)))
                                                                  node)))))))))
           (%refnode-p (node) (refnode-p node refmark)))
    (rec routeref-diff (list 0))))

(defun refnode-p (node refmark)
  (and (proper-list-p node) (eq (car node) refmark)))

(defun lostnode-p (node dismark)
  (and (proper-list-p node) (eq (car node) dismark)))

(printing-let* ((base '(lambda (x)
                         (showdiff *first-impl* *second-impl* x)
                         (write-line "br/<")))
                (modified '(lambda (x)
                             (princ x)
                             (print (showdiff *first-impl* *second-impl* x))))
                (newnode-detected-diff  (rdiff base modified 'ref 1))
                (lost-detected-diff (lost-subtree-list newnode-detected-diff base 'ref 'lost)))
               newnode-detected-diff
               lost-detected-diff
               (merge-lost newnode-detected-diff lost-detected-diff 'ref))

(defun output-diff-as-html (base modified &optional (stream *standard-output*) (allowed-distance 1))
  (let* ((*standard-output* stream)
         (refmark (gensym)) (dismark (gensym))
         (newnode-detected-diff (rdiff base modified refmark allowed-distance))
         (lost-detected-diff (lost-subtree-list newnode-detected-diff base refmark dismark)))
    (write-line "<html> <head><title></title></head> <body bgcolor=\"000000\"><p>")
    (with-route (cur route) (merge-lost newnode-detected-diff lost-detected-diff refmark)
      (cond ((refnode-p cur refmark) (white (retrieve-by-route base (route-normalize (drop cur)))))
            ((lostnode-p cur dismark) (red (retrieve-by-route base (route-normalize (drop cur)))))
            ((atom cur) (green cur))
            (t (white "(") next-level (white ")"))))
  (write-line "</p></body></html>")))

(with-open-file (out "tmp.html" :direction :output :if-does-not-exist :create :if-exists :supersede)
  (output-diff-as-html '(lambda (x)
                          (showdiff *first-impl* *second-impl* x)
                          (write-line "br/>"))
                       '(lambda (x)
                          (princ x)
                          (print (showdiff *first-impl* *second-impl* x)))
                       out 2))

(with-open-file (out "tmp.html" :direction :output :if-does-not-exist :create :if-exists :supersede)
  (output-diff-as-html *first-impl* *first-impl* out 1)
  (output-diff-as-html *second-impl* *second-impl* out 1)
  (output-diff-as-html *first-impl* *second-impl* out 1)
  (output-diff-as-html *first-impl* *third-impl* out 1)
  (output-diff-as-html *first-impl* *third-impl* out 1)
  (output-diff-as-html *first-impl* *fourth-impl* out 1)
  (output-diff-as-html *first-impl* *fifth-impl* out 1)
  (output-diff-as-html *first-impl* *impl1* out 1)
  (output-diff-as-html *impl1* *first-impl* out 1)
  (output-diff-as-html *second-impl* *first-impl* out 1)
  (output-diff-as-html '(x y z w) '(x z w) out 1))

(printing-let* ((base *first-impl*)
                (modified *impl1*)
                (newnode-detected-diff  (rdiff base modified 'ref 1))
                (lost-detected-diff (lost-subtree-list newnode-detected-diff base 'ref 'lost)))
               newnode-detected-diff
               lost-detected-diff
               (merge-lost newnode-detected-diff lost-detected-diff 'ref))

(with-open-file (out "tmp.html" :direction :output :if-does-not-exist :create :if-exists :supersede)
  (output-diff-as-html '(lambda (x)
                          (showdiff *first-impl* *second-impl* x)
                          (write-line "br/>"))
                       '(lambda (x)
                          (princ x)
                          (print (showdiff *first-impl* *second-impl* x)))
                       out 2))
