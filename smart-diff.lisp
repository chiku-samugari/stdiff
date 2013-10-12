(defun smart-diff (basis modified ref-mark identity-sym dummy-sym)
  (let ((subtrees (collect-effective-refs basis)))
    (labels ((rec (basis modified)
               (acond ((equal basis modified) identity-sym)
                      ((find-if (lambda (x) (equal modified x))
                                subtrees :key #'third)
                       (cons ref-mark (car it)))
                      ((and (consp basis) (consp modified))
                       (mapcar-along-longer #'rec basis modified dummy-sym))
                      (t modified))))
      (rec basis modified))))

(defun lengthen-list (n lst &optional fill-value)
  (do ((i 0 (1+ i)) (alt-lst lst (cdr alt-lst)))
    ((<= n i) lst)
    (if (null alt-lst)
      (return (append lst (make-list (- n i) :initial-element fill-value))))))

;(lengthen-list 10 (iota 7))
;(lengthen-list 10 (iota 7) (gensym))

(defun mapcar-along-longer (fn lst0 lst1 &optional (fill-value nil))
  (let ((len (length (longest lst0 lst1))))
    (mapcar fn
            (lengthen-list len lst0 fill-value)
            (lengthen-list len lst1 fill-value))))

(defun longest (&rest lsts)
  (do ((scanning (cdr lsts) (cdr scanning))
       (answer (car lsts)
               (if (shorter answer (car scanning))
                 (car scanning)
                 answer)))
    ((null scanning) answer)))

(smart-diff *first-impl* *second-impl* 'ref '- 'empty)

(simple-diff
  (smart-diff *first-impl* *second-impl* 'ref '- 'empty)
  (simple-diff *first-impl* *second-impl* '- 'empty)
  'same 'disappear)

(smart-diff *first-impl* *impl1* 'subtree-reference '- 'empty)

(smart-diff *first-impl* *alt-third-impl* 'ref '- 'empty)

(smart-diff *third-impl* *alt-third-impl* 'ref '- 'empty)
(smart-diff *third-impl* *second-impl* 'ref '- 'empty)

(defun alt-smart-diff% (base modified ref-mark identity-sym)
  (let ((base-subtrees (collect-effective-refs base)))
    (format t "~{~a~%~}" base-subtrees)
    (labels ((rec (modified route)
               (format t "~a : ~a~%" route modified)
               (acond ((remove-if-not (papply #'equal modified)
                                      base-subtrees :key #'last1)
                       (if (member route it :key #'second :test #'equal)
                         identity-sym
                         (cons ref-mark (caar it))))
                      ((atom modified) modified)
                      (t (loop for idx = 0 then (1+ idx)
                               for elem in modified
                               collect (rec elem (cons idx route)))))))
      (rec modified (list 0)))))

(COLLECT-EFFECTIVE-REFS *third-impl*)

(alt-smart-diff% *first-impl* *second-impl* 'ref '-)
(alt-smart-diff% *first-impl* *impl1* 'ref '-)
(alt-smart-diff% *first-impl* `(progn ,*first-impl*) 'ref '-)
(alt-smart-diff% *third-impl* *alt-third-impl* 'ref '-)
(alt-smart-diff% *third-impl* *second-impl* 'ref '-)

(alt-smart-diff% '(x y z w) '(x z w) 'ref '-)

(smart-diff '(x y z w) '(x z w) 'ref '- 'empty)

(simple-diff '(x y z w) '(x z w) '- 'empty)

(defun revert-alt-smart-diff% (base diff ref-mark identity-sym dummy-sym)
  (let ((base-subtrees (collect-effective-refs base)))
    (labels ((rec (diff route)
               (cond ((eq diff identity-sym)
                      (last1 (find-if (papply #'equal route) base-subtrees :key #'second)))
                     ((and (consp diff) (eq (car diff) ref-mark))
                      (last1 (find-if (papply #'= (cdr diff))
                                      base-subtrees :key #'car)))
                     ((consp diff)
                      (loop for idx = 0 then (1+ idx)
                            for elem in diff
                            collect (rec elem (cons idx route))))
                     (t diff))))
      (rec diff (list 0)))))

(equal *alt-third-impl*
       (revert-alt-smart-diff% *third-impl*
                               (alt-smart-diff% *third-impl* *alt-third-impl*
                                                'ref '-)
                               'ref
                               '-
                               'empty))

(alt-smart-diff% *first-impl* *impl1* 'ref '-)
(smart-diff *first-impl* *impl1* 'ref '- 'dummy)
