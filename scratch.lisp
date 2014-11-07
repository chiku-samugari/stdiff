(in-package :stdiff)

(let ((base '(lambda (x)
               (showdiff *first-impl* *second-impl* x)
               (write-line "br/>")))
      (modified '(lambda (x)
                   (princ x)
                   (showdiff *first-impl* *second-impl* x)
                   (write-line "br/>"))))
  (with-route (node r) 
              (let (tmp)
                (with-route (cur route) modified
                  (LABELS ((G936 (ROUTE)
                             (ACOND
                               ((AND
                                  (NOTANY
                                    (PAPPLY (START-WITH (ROUTE-NORMALIZE ROUTE) (FUNCALL _ :ROUTE)))
                                    TMP)
                                  (NOTANY
                                    (PAPPLY (START-WITH (FUNCALL _ :ROUTE) (ROUTE-NORMALIZE ROUTE)))
                                    TMP))
                                (CAR (PUSH (RESERVE-ROUTE ROUTE CUR) TMP)))
                               ((REMOVE-IF-NOT
                                  (PAPPLY (START-WITH (ROUTE-NORMALIZE ROUTE) (FUNCALL _ :ROUTE)))
                                  TMP)
                                (PROGN
                                  (MAPC (PAPPLY (FUNCALL _ :CANCEL)) IT)
                                  (CAR (PUSH (RESERVE-ROUTE ROUTE CUR) TMP))))
                               (T NEXT-LEVEL))))
                    (COND
                      ((EQUAL CUR (RETRIEVE-BY-ROUTE BASE (ROUTE-NORMALIZE ROUTE)))
                        (LET ((ROUTE937 ROUTE))
                             (G936 ROUTE937)))
                      ((SOME (LAMBDA (X) (AND (<= (LEVENSHTEIN-DISTANCE ROUTE X) 1) X))
                             (FIND-ROUTE CUR BASE))
                       (LET ((ROUTE937
                               (SOME (LAMBDA (X) (AND (<= (LEVENSHTEIN-DISTANCE ROUTE X) 1) X))
                                     (FIND-ROUTE CUR BASE))))
                            (G936 ROUTE937)))
                      (T NEXT-LEVEL)))))))

(with-route (node route) *impl1*
            (print route) (print node)
            next-level)

(setq vdefun0
      '(defmacro vdefun (name params &body body)
         (with-gensyms (args result)
           `(progn
              (if already-fbound? (fmakunbound 'name))
              (defun ,name (,@params) ,@body)

              (set-current-impl-entry
                ',name
                (add-impl ',name
                          `(defun ,',name ,',params ,@',body)
                          #',name))

              (run-test ',name)

              (defun ,name (&rest ,args)
                (destructuring-bind (,@params)
                  ,args
                  (let ((,result (progn ,@body)))
                    (add-rindoh-entry ',name `(,',name ,@,args)
                                      (gen-rindoh-entry (lambda () (with-raw-fn (,name)
                                                                     (equal (apply #',name ,args) ,result)))
                                                        ,result
                                                        #'equal
                                                        `(equal (,',name ,@,args) ,,result)))
                    ,result)))))))

(setq vdefun1
      '(defmacro vdefun (name params &body body)
         (with-gensyms (args result)
           `(progn
              (let ((already-fbound? (fboundp ',name)))
                ;; If a function whose name is ``NAME'' has already been
                ;; defined, then the warning message at this point should be
                ;; surpressed.
                (if already-fbound? (fmakunbound 'name))
                (defun ,name (,@params) ,@body)

                (set-current-impl-entry
                  ',name
                  (add-impl ',name
                            `(defun ,',name ,',params ,@',body)
                            #',name))

                (run-test ',name)

                ;; If a function whose name is ``NAME'' has not yet been
                ;; defined, then the warning message at this point should be
                ;; surpressed.
                (if (not already-fbound?) (fmakunbound 'name))

                (defun ,name (&rest ,args)
                  (destructuring-bind (,@params)
                    ,args
                    (let ((,result (progn ,@body)))
                      (add-rindoh-entry ',name `(,',name ,@,args)
                                        (gen-rindoh-entry (lambda () (with-raw-fn (,name)
                                                                       (equal (apply #',name ,args) ,result)))
                                                          ,result
                                                          #'equal
                                                          `(equal (,',name ,@,args) ,,result)))
                      ,result))))))))

(pphtml::output-as-html
  (format nil "<pre>~a</pre>"
          (pphtml::pair-coloring
            "({" "})" #'pphtml::green
            (pphtml::pair-coloring
              "([" "])" #'pphtml::red
              (stdiff::bracebracket vdefun0 vdefun1))))
  "tmp.html")

(asdf:load-system  :pphtml)
(use-package :pphtml)

(output-as-html (format nil "<pre>~a</pre>"
                        (pair-coloring
                          "({" "})"
                          #'pphtml::green
                          (pair-coloring "([" "])"
                                        #'pphtml::red
                                        (bracebracket *first-impl* *third-impl* 0))))
                "tmp.html")

(output-as-html (format nil "<pre>~a</pre>"
                        (pair-coloring "({" "})" #'pphtml::green
                                      (pair-coloring "([" "])" #'pphtml::red
                                                    (bracebracket *second-impl* *first-impl* 0))))
                "tmp.html")

(output-as-html
  (reduce #'(concat-str
              _ (format nil "<pre>~a</pre>"
                        (pair-coloring
                          "({" "})" #'pphtml::green
                          (pair-coloring
                            "([" "])" #'pphtml::red
                            (print (bracebracket *seqlast2* (list 'progn *seqlast2*) _))))))
          (iota 5) :initial-value "")
  "tmp.html")

(bracebracket '(x y z w) '(x y a z w ) 3)
(bracebracket '(x) '(w))
(rdiff *seqlast2* `(progn ,*seqlast2*) 'ref 0)
(lost-subtree-list (rdiff  *seqlast2* `(progn ,*seqlast2*) 'ref 0) *seqlast2* 'ref 'lost)
(lost-subtree-list (rdiff  *seqlast2* *seqlast0* 'ref 0) *seqlast2* 'ref 'lost)
(lost-subtree-list (rdiff  '(x) '(w) 'ref 0) '(x) 'ref 'lost)
(stdiff '(x) '(w) 'ref 'lost)

(bracebracket 'a 'x)
(stdiff 'a 'x 'ref 'lost 1)
(lost-subtree-list (rdiff 'a 'x 'ref 1) 'a 'ref 'lost)

(diff (list ()) (list () () ()))

(printing-let* ((dist 5)
                (base '(a (x y ((((w) b) c) d)) s ((u))))
                (modified '(a z w u))
                (refdiff (rdiff base modified 'ref dist))
                (lostnodes (lostnode-list (rdiff base modified 'ref dist) base 'ref 'lost)))
  lostnodes
  (mapcar #'(retrieve-by-route base (route-normalize (drop _)))
          lostnodes)
  refdiff
  (merge-lost refdiff lostnodes 'ref)
  (stdiff-cl:stdiff-terminal base modified dist))

(printing-let* ((dist 2) (base '(a (x y z w) ((b)))) (modified '(a (y))))
  (stdiff-cl:stdiff-terminal base modified dist))

(printing-let* ((dist 2) (base '(a (x y z w))) (modified '(a y)))
  (stdiff-cl:stdiff-terminal base modified dist))

(printing-let* ((dist 2) (base '(a b (k (x y z w)))) (modified '(a y))
                         (lostnodes (lostnode-list (rdiff base modified 'ref dist) base 'ref 'lost)))
  lostnodes
  (stdiff-cl:stdiff-terminal base modified dist))
