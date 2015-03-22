#lang s-exp rosette
(provide acl
         acl-list
         secgroup
         config
         check-direct-connection
         test-config
 )

;;----------------------------------------------------------------------------------------------------------------------------------
(require rosette/solver/smt/z3 rosette/solver/kodkod/kodkod (only-in racket new string-split string->number symbol->string error))
(current-solver (new kodkod%)) ;Want minimal extraction for now?

(struct acl-struct (grants ; symbol
                    port-range) ;pair of ints
  #:transparent)

(struct instance-struct (name ; symbol
                         group) ; symbol
  #:transparent)

(struct sg-struct (name ; symbol
                   inbound ; list of ACLs
                   outbound) ;list of ACLs
  #:transparent)

(struct config-struct (secgroups ;Hash of sg-struct
                       vms) ;Hash of vm-struct
  #:transparent)

;;----------------------------------------------------------------------------------------------------------------------------------------------

(define (zip . lists) (apply map list lists))

(define (instance name group) (instance-struct name group))

(define (symbol->ports sym)
  (cond
    [(number? sym) (cons sym sym)]
    [else (let* [(split (string-split (symbol->string sym) "-"))
                 (lsplit (length split))]
            (cond
              [(= lsplit 1) (string->number (car split))]
              [(= lsplit 2) (cons (string->number (car split)) (string->number (car (cdr split))))]
              [else (error "Don't know how to interpret port")]
              ))]))

(define-syntax acl
  (syntax-rules (-)
    [(acl grant start - end) (acl-struct grant (cons start end))]
    [(acl grant port) (acl-struct grant (symbol->ports (quote port)))]))

(define-syntax acl-list
  (syntax-rules ()
    [(acl-list [grant ...] ...) (list (acl grant ...) ...)]
    [(acl-list) (list)]))


(define-syntax-rule (secgroup group [inbound ...] [outbound ...])
  (sg-struct group (acl-list inbound ...) (acl-list outbound ...)))

(define-syntax-rule 
  (config [(group inbound outbound) ...] [(name sg) ...])
  (config-struct (apply hash (flatten (zip (list world group ...) (list world-secgroup (secgroup group inbound outbound) ...))))
                 (apply hash (flatten (zip (list name ...) (list (instance name sg) ...))))))

;;---------------------------------------------------------------------------------------------------------------------------------------------------

(define world 'any) ; Designate a thing to be outside

(define world-secgroup 
  (secgroup world [(world 1-65535)] [(world 1-65535)]))



;; --------------------------------------------------------------------------------------------------------------------------------------------------

(define (grant-group-eq? grant group)
  (-> symbol? symbol? boolean?)
  (cond
    [(eq? grant world) #t]
    [else (eq? grant group)]))

(define (acls-allows-group acls group port)
  (-> list? symbol? number? boolean?)
  (cond
    [(empty? acls) #f]
    [else 
     (let*
        [(grant (acl-struct-grants (car acls)))
         (port-low (car (acl-struct-port-range (car acls))))
         (port-high (cdr (acl-struct-port-range (car acls))))]
       (cond
         [(and (grant-group-eq? grant group) (<= port-low port) (<= port port-high)) #t]
         [else (acls-allows-group (cdr acls) group port)]))]))

;; Check if one can directly connect between two machines
(define (check-direct-connection configuration machine1 machine2 port)
  (-> config-struct? symbol? symbol? number? boolean?)
  (let* 
      [(machinegroups (config-struct-vms configuration))
       (secgroups (config-struct-secgroups configuration))
       (m1secgroup (instance-struct-group (hash-ref machinegroups machine1 (instance machine1 world))))
       (m2secgroup (instance-struct-group (hash-ref machinegroups machine2 (instance machine2 world))))
       (m1outbound (sg-struct-outbound (hash-ref secgroups m1secgroup)))
       (m2inbound (sg-struct-inbound (hash-ref secgroups m2secgroup)))]
    (and (acls-allows-group m1outbound m2secgroup port)
         (acls-allows-group m2inbound m1secgroup port))))


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