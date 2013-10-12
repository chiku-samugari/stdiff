(in-package :chiku.diff)

(defun simple-diff (base modified identity-sym dummy-sym)
  (cond ((equal base modified) identity-sym)
        ((and (consp base) (consp modified))
         (mapcar-along-longer
           (papply #'simple-diff _ _ identity-sym dummy-sym)
           base modified dummy-sym))
        (t modified)))

(simple-diff *first-impl* *second-impl* '- 'empty)

(simple-diff *first-impl* *third-impl* '- 'empty)
