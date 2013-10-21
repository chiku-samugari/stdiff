(in-package :stdiff)

(defvar *first-impl*
  '(defun iota (n)
     (let (lst)
       (dotimes (i n (nreverse lst))
         (push i lst)))))

(defvar *second-impl*
  '(defun iota (n &optional (start 0))
     (let (lst)
       (dotimes (i n (nreverse lst))
         (push (+ i start) lst)))))

(defvar *third-impl*
  '(defun iota (n &optional (start 0) (step 1))
     (let (result)
       (dotimes (i n (nreverse result))
         (push (+ (* i step) start) result)))))

(defparameter *alt-third-impl*
  '(defun iota (n &optional (start 0) (step 1))
     (let (lst)
       (dotimes (i n (nreverse lst))
         (push (+ (* i step) start) lst)))))

(defvar *fourth-impl*
  '(defun iota (n &optional (start 0) (step 1))
    (loop for i from 0 upto (1- n) collect (+ (* i step) start))))

(defvar *fifth-impl*
  '(defun iota (n &optional (start 0) (step 1))
     (loop for i from 0 to (1- n)
           collect (+ (* i step) start))))

(defparameter *impl1*
  '(defun iota (n)
     (if (< n 0)
       (error "Negative N is given : ~a." n)
       (let (lst)
         (dotimes (i n (nreverse lst))
           (push i lst))))))

(defparameter *impl2*
  '(defun iota (n)
     "THING"
     (progn
       (if (< n 0) (ERROR "Negative N is given : ~a." n)
         (let (lst)
           (dotimes (i n (nreverse lst)) (push i lst)))))
     "SOMETHING"))

(defvar *seqlast0*
  '(defun seqlast (seq)
     (subseq seq (1- (length seq)))))

(defvar *seqlast1*
  '(defun seqlast (seq &optional (n 1))
     (subseq seq (- (length seq) n))))

(defvar *seqlast2*
  '(defun seqlast (seq &optional (n 1))
     (ctypecase seq
       (cons (last seq n))
       (subseq seq (- (length seq) n)))))
