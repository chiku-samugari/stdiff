(defpackage :stdiff-use-sample
  (:use :cl :chiku.util :stdiff))

(in-package :stdiff-use-sample)

(defun wrap-by-bracket (expr)
  (list '[ expr ']))

(defun wrap-by-brace (expr)
  (list '{ expr '}))

(defun bracebracket (base modified &optional (allowed-distance 0))
  (with-gensyms (refmark lostmark)
    (apply-modifiednode-converters
      (stdiff base modified refmark lostmark allowed-distance)
      base refmark lostmark #'wrap-by-brace #'wrap-by-bracket)))

;(bracebracket *first-impl* *second-impl*)

(require :pphtml)

(use-package :pphtml)

(defun show-stdiff-cl (base modified outhtml-pathspec &optional (allowed-distance 0))
  (output-as-html (format nil "<pre>~a</pre>"
                          (pair-coloring
                            "({" "})"
                            #'pphtml::green
                            (pair-coloring "([" "])"
                                           #'pphtml::red
                                           (bracebracket base modified allowed-distance))))
                  outhtml-pathspec))

(load "impls.lisp")

(show-stdiff-cl *first-impl* *third-impl* "tmp.html")