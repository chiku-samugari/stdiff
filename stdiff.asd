(defpackage :stdiff.asd
  (:use :cl :asdf))

(in-package :stdiff.asd)

(defsystem :stdiff
  :version "0.4.0"
  :maintainer "Takehiko Nawata"
  :author "Takehiko Nawata"
  :license "MIT License"
  :description "STDIFF"
  :long-description "STDIFF : Syntax tree diff for Common Lisp."
  :serial t
  :components ((:file "packages")
               (:file "stdiff")))
