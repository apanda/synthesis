#lang s-exp rosette
#;(provide acl
         acl-list
         secgroup
         config
         check-direct-connection
         check-indirect-connection
         test-config
         test-config2
         test-config3
 )
(provide (all-defined-out))

;;----------------------------------------------------------------------------------------------------------------------------------
(require rosette/solver/smt/z3 rosette/solver/kodkod/kodkod
         (only-in racket new string-split string->number symbol->string error number->string string-append))
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
  (config-struct (apply hash (flatten (zip (list world group ...)
                                           (list world-secgroup (secgroup group inbound outbound) ...))))
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

(define (acl-allows-group acl group port)
  (-> acl-struct? symbol? boolean?)
  (let*
     [(grant (acl-struct-grants acl))
      (port-low (car (acl-struct-port-range acl)))
      (port-high (cdr (acl-struct-port-range acl)))]
      (and (grant-group-eq? grant group) (<= port-low port) (<= port port-high))))

(define (acl-allows-port acl port)
  (-> acl-struct? symbol? boolean?)
  (let*
     [(port-low (car (acl-struct-port-range acl)))
      (port-high (cdr (acl-struct-port-range acl)))]
      (and (<= port-low port) (<= port port-high))))

(define (acls-allow-group acls group port)
  (-> list? symbol? number? boolean?)
  (cond
    [(empty? acls) #f]
    [else 
       (cond
         [(acl-allows-group (car acls) group port) #t]
         [else (acls-allow-group (cdr acls) group port)])]))

(define (check-direct-connection-sg configuration srcsg destsg port)
  (-> config-struct? symbol? symbol? number? boolean?)
  (let* 
      [(secgroups (config-struct-secgroups configuration))
       (m1outbound (sg-struct-outbound (hash-ref secgroups srcsg)))
       (m2inbound (sg-struct-inbound (hash-ref secgroups destsg)))]
    (and (acls-allow-group m1outbound destsg port)
         (acls-allow-group m2inbound srcsg port))))

(define (all-accessible-groups configuration group port)
  (-> config-struct? symbol? number? boolean?)
  (let*
    [(secgroups (config-struct-secgroups configuration))
     (inbound (sg-struct-inbound (hash-ref secgroups group)))
     (inbound-allowed (map acl-struct-grants (filter (curryr acl-allows-port port) inbound)))
     (outbound-rules (map (lambda (sg) (cons sg (sg-struct-outbound (hash-ref secgroups sg)))) inbound-allowed))
     (outbound-allowed (filter (lambda (p) (acls-allow-group (cdr p) group port)) outbound-rules))
     (outbound-clean (map (lambda (p) (car p)) outbound-allowed))]
   outbound-clean))

(define (machine-exists? configuration secgroup)
  (member secgroup (remove-duplicates (map instance-struct-group (hash-values (config-struct-vms configuration))))))

(define (check-indirect-connection-internal configuration srcSG targetSG port explored)
  (-> config-struct? symbol? symbol? number? list? boolean?)
  (cond
    [(check-direct-connection-sg configuration srcSG targetSG port) #t]
    [else
      (let*
        [(connected-targets (all-accessible-groups configuration targetSG port))
         (new-explored (remove-duplicates (append explored connected-targets)))
         (to-explore (filter (curry machine-exists? configuration) 
                             (filter (compose not (curryr member explored)) connected-targets)))
         (explore-result (map (lambda (target) 
                                (check-indirect-connection-internal configuration srcSG target port new-explored))
                              to-explore))]
        (not (empty? (filter identity explore-result))))]))

;; Check if one can directly connect between two machines
(define (check-direct-connection configuration machine1 machine2 port)
  (-> config-struct? symbol? symbol? number? boolean?)
  (let* 
      [(machinegroups (config-struct-vms configuration))
       (m1secgroup (instance-struct-group (hash-ref machinegroups machine1 (instance machine1 world))))
       (m2secgroup (instance-struct-group (hash-ref machinegroups machine2 (instance machine2 world))))]
      (check-direct-connection-sg configuration m1secgroup m2secgroup port)))

;; Check if one can indirectly connect between two machines
(define (check-indirect-connection configuration src target port)
  (-> config-struct? symbol? symbol? number? boolean?)
  (let*
    [(machinegroups (config-struct-vms configuration))
     (srcSG (instance-struct-group (hash-ref machinegroups src (instance src world))))
     (targetSG (instance-struct-group (hash-ref machinegroups target (instance target world))))]
    (cond 
      [(check-direct-connection-sg configuration srcSG targetSG port) #t]
      [else (check-indirect-connection-internal configuration srcSG targetSG port (list srcSG targetSG))])))

(define (should-modify configuration)
  (let*
      [(new-symbolic (lambda () (define-symbolic* x boolean?) x))]
    (zip (hash-keys (config-struct-secgroups configuration))
         (map (lambda (i) (new-symbolic)) (range 0 (length (hash-keys (config-struct-secgroups configuration)))))
         (map (lambda (i) (new-symbolic)) (range 0 (length (hash-keys (config-struct-secgroups configuration))))))))

(define (get-secgroup configuration idx)
  (let*
      [(sg-names (hash-keys (config-struct-secgroups configuration)))]
    (list-ref sg-names idx)))

(define (symbolic-get-secgroup configuration idx-symb)
  (let*
      [(sg-names (hash-keys (config-struct-secgroups configuration)))]
    (assert (< idx-symb (length sg-names))))
  (assert (<= 0 idx-symb))
  (get-secgroup configuration idx-symb))

(define (add-inbound-acl configuration sg rule)
  (-> config-struct? config-struct?)
  (let*
      [(secgroups (config-struct-secgroups configuration))
       (instances (config-struct-vms configuration))]
    (config-struct
    (hash-update secgroups sg 
                 (lambda (s)  
                   (sg-struct (sg-struct-name s)
                              (cons rule (sg-struct-inbound s))
                              (sg-struct-outbound s))))
    instances)))
     
(define (add-outbound-acl configuration sg rule)
  (-> config-struct? config-struct?)
  (let*
      [(secgroups (config-struct-secgroups configuration))
       (instances (config-struct-vms configuration))]
    (config-struct
    (hash-update secgroups sg 
                 (lambda (s)  
                   (sg-struct (sg-struct-name s)
                              (sg-struct-inbound s)
                              (cons rule (sg-struct-outbound s)))))
    instances)))

(define (new-symbolic-acl configuration)
  (-> config-struct? acl-struct?)
  (let* [(new-symbolic-sg (lambda () (define-symbolic* group number?) group))
         (new-symbolic-port (lambda () (define-symbolic* port number?) port))
         (secgroup (symbolic-get-secgroup configuration (new-symbolic-sg)))
         (portLow (new-symbolic-port))
         (portHigh (new-symbolic-port))]
    (acl secgroup portLow - portHigh)))

(define (symbolic-configuration-change configuration)
  (-> config-struct? config-struct?)
  (let* [(modify-config (should-modify configuration))]
    (displayln modify-config)
    (foldl
     (lambda (modify cfg)
       (let* [(sgname (car modify))
              (i-mod (cadr modify))
              (o-mod (caddr modify))
              (mod-i (if i-mod (add-inbound-acl cfg sgname (new-symbolic-acl cfg)) cfg))
              (mod-o (if o-mod (add-outbound-acl mod-i sgname (new-symbolic-acl mod-i)) mod-i))]
         mod-o)) configuration modify-config)))

#;(define (symbolic-configuration configuration)
  (-> config-struct? config-struct?)
  (let* [(new-symbolic-boolean (lambda () (define-symbolic* x boolean?) x))
         (sec-group-list (hash->list (config-struct-secgroups configuration)))
         (modsg 
          (map (lambda pr 
                 (let* [(sgname (car pr))
                        (sg (cdr pr))
                        (inbound (sg-struct-inbound sg))
                        (outbound (sg-struct-outbound sg))
                        (mod-i (if (new-symbolic-boolean) 
                                   (cons (new-symbolic-acl configuration) inbound) inbound))
                        (mod-o (if (new-symbolic-boolean)
                                   (cons (new-symbolic-acl configuration) outbound) outbound))]
                   (cons sgname (sg-struct sgname mod-i mod-o)))) sec-group-list))
         (vms (config-struct-vms configuration))]
    (flatten modsg)))

(define (symbolic-configuration configuration)
  (-> config-struct? config-struct?)
  (let* [(new-symbolic-boolean (lambda () (define-symbolic* x boolean?) x))
         (sec-group-list (hash->list (config-struct-secgroups configuration)))
         (modsg 
          (map (lambda pr 
                 (let* [(sgname (caar pr))
                        (sg (cdar pr))
                        (in (sg-struct-inbound sg))
                        (out (sg-struct-outbound sg))
                        (mod-in (if (new-symbolic-boolean) (cons (new-symbolic-acl configuration) in) in))
                        (mod-out (if (new-symbolic-boolean) (cons (new-symbolic-acl configuration) out) out))
                        (nsg (sg-struct sgname mod-in mod-out))
                        (nl (cons sgname nsg))]
                   nl)) sec-group-list))
         (vms (config-struct-vms configuration))]
    (config-struct (apply hash (flatten modsg)) vms)))

;;---------------------------------------------------------------------------------------------------------------
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
