'(a b c)

'(progn (a b c))

'(progn (let (x)
          (a b c)))

'(progn (let* (x)
         (a b c)))

'(progn (progn (a b c)))

(alt-smart-diff%
  '(progn (a b c))
  '(progn (let (x)
            (a b c)))
  'ref '-)

'(list (a b c) (x y z) (a b c))
'(progn (list (x y z) (a b c) (s t u) (a b c)))
'(list (let ? (x y z) (a b c) (s t u) (a b c)))

(alt-smart-diff%
  '(progn (list (x y z) (a b c) (s t u) (a b c)))
  '(list (let ? (x y z) (a b c) (s t u) (a b c)))
  'ref '-)

'(list (a b c) (x y z) (a b c))
;;; Following should be recognized as a WRAP operation.
'(progn
   (list (x y z) (a b c) (s t u) (a b c)))
;;; Reason:
'(equal (route '(progn (list (x y z) (a b c) (s t u) (a b c)))
               '(progn (list (x y z) (a b c) (s t u) (a b c))))
        (route '(list (x y z) (a b c) (s t u) (a b c))
               '(list (x y z) (a b c) (s t u) (a b c))))
;;; Next example may be distinguished from the above one:
'(let ((i 0))
   (x y z) (a b c) (s t u) (a b c))
;;; More general example:
'(let ((i 0))
   (x y z) (a b c) (s t u) (a b c)
   do more things)
;;; How about reader macro?
;;; *READ-SUPPRESS* can be a part of solution.
