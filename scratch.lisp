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
