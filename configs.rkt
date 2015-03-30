#lang s-exp rosette
(provide (all-defined-out))
(require "sem.rkt")
(define test-config 
  (config
   [('frontend
     [('frontend 1-65535)
     (world 22)]
     [('frontend 1-65535)
      ('backend 1-65535)])
    ('backend
     [('backend 1-65535)]
     [('backend 1-65535)
      (world 22)])]
   [('a 'frontend) ('b 'backend) ('c 'frontend)]))

(define test-config2
  (config
   [('frontend
     [('frontend 1-65535)
     (world 22)]
     [('frontend 1-65535)
      ('backend 1-65535)])
    ('backend
     [('backend 1-65535)
      ('frontend 1-65535)]
     [('backend 1-65535)
      (world 22)])]
   [('a 'frontend) ('b 'backend) ('c 'frontend)]))


(define test-config3
  (config
    [('sg1
      [('sg1 1-65535)
       ('sg2 1-65535)]
      [('sg1 1-65535)])
     ('sg2
      [('sg2 1-65535)
       ('sg3 1-65535)]
      [('sg1 1-65535)
       ('sg2 1-65535)])
     ('sg3
      [(world 22)
       (world 80)
       ('sg3 1-65535)]
      [('sg2 1-65535)
       ('sg3 1-65535)])]
    [('a 'sg1) ('b 'sg2) ('c 'sg3)]))

(define test-config4
  (config
    [('sg1
      [('sg1 1-65535)
       ('sg2 1-65535)]
      [('sg1 1-65535)])
     ('sg2
      [('sg2 1-65535)
       ('sg3 1-65535)]
      [('sg1 1-65535)
       ('sg2 1-65535)])
     ('sg3
      [(world 22)
       (world 80)
       ('sg3 1-65535)]
      [('sg2 1-65535)
       ('sg3 1-65535)])]
    [('a 'sg1) ('c 'sg3)]))
