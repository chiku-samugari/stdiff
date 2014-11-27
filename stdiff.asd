(defpackage :stdiff.asd
  (:use :cl :asdf))

(in-package :stdiff.asd)

(defsystem :stdiff
  :version "0.6.0"
  :maintainer "Takehiko Nawata"
  :author "Takehiko Nawata"
  :license "MIT License"
  :description "STDIFF"
  :long-description "STDIFF : Symbol Tree Diff."
  :depends-on (:chiku.util :papply)
  :serial t
  :components ((:file "packages")
               (:file "stdiff")))
