#lang racket
(require rackunit 
         "../sem.rkt")

  (check-eq? (check-direct-connection test-config 'a 'b 22) #f)
  (check-eq? (check-direct-connection test-config 'a 'c 22) #t)
  (check-eq? (check-direct-connection test-config 'd 'a 22) #t)
  (check-eq? (check-direct-connection test-config 'a 'd 22) #f)
  (check-eq? (check-direct-connection test-config 'b 'd 22) #t)
  (check-eq? (check-direct-connection test-config 'b 'd 80) #f)
