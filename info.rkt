#lang info
(define collection "abt")
(define deps '("base"
               "rackunit-lib"
               "zippers"))
(define build-deps '("scribble-lib" "racket-doc"))
(define scribblings '(("scribblings/abt.scrbl" ())))
(define pkg-desc "Abstract binding trees")
(define version "0.0")
(define pkg-authors '("David Christiansen"))
