#lang racket/base
;; The functions the extraction left out, as the knowledge check names them
;; (pipeline/check-knowledge.rkt): a protocol calling one is noted, not a problem.
(require rackunit racket/file "../lib/pipeline/check-knowledge.rkt")

(define dir (make-temporary-file "cs-left-out-~a" 'directory))
(check-equal? (left-out-reasons dir) (hash))
(with-output-to-file (build-path dir "left-out.rktd")
  (lambda ()
    (writeln '("ostd::mm::frame::segment::impl&%1::_VERUS_VERIFIED_from_unused" closure-bound))
    (writeln '("ostd::mm::frame::meta::impl&%1::get_from_in_use" type))))
(define h (left-out-reasons dir))
(check-equal? (hash-ref h 'mm::frame::segment::impl&%1::from_unused #f) 'closure-bound)
(check-equal? (hash-ref h 'mm::frame::meta::impl&%1::get_from_in_use #f) 'type)
(check-false (hash-ref h 'mm::frame::segment::impl&%1::split #f))
(delete-directory/files dir)
