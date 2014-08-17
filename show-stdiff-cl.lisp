(require :asdf)

(require :stdiff)

(require :pphtml)

(defpackage :stdiff-use-sample
  (:use :cl :chiku.util :stdiff :pphtml))

(in-package :stdiff-use-sample)

(defun wrap-by-bracket (expr)
  (list '[ expr ']))

(defun wrap-by-brace (expr)
  (list '{ expr '}))

(defun bracebracket (base modified &optional (allowed-distance 0))
  (with-gensyms (refmark lostmark)
    (apply-modifiednode-converters
      (diff base modified refmark lostmark allowed-distance)
      base refmark lostmark #'wrap-by-brace #'wrap-by-bracket)))

(defun show-stdiff-cl (base modified outhtml-pathspec &optional (allowed-distance 0))
  (output-as-html (format nil "<pre>~a</pre>"
                          (pair-coloring
                            "({" "})"
                            #'pphtml::green
                            (pair-coloring "([" "])"
                                           #'pphtml::red
                                           (bracebracket base modified allowed-distance))))
                  outhtml-pathspec))

(show-stdiff-cl '(defmacro list/det% (&body clauses)
                   (if clauses
                     (let ((head (car clauses)))
                       `(if ,(car head)
                          (cons ,(cadr head) (list/det% ,@(cdr clauses)))
                          (list/det% ,@(cdr clauses))))))
                '(defmacro list/det% (&body clauses)
                   (if clauses
                     (let ((head (car clauses)))
                       (if (eq (car head) t)
                         `(cons ,(cadr head) (list/det% ,@(cdr clauses)))
                         `(if ,(car head)
                            (cons ,(cadr head) (list/det% ,@(cdr clauses)))
                            (list/det% ,@(cdr clauses)))))))
                "list-with-determiner.html" 1)
