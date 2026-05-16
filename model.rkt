#lang racket

(require redex)


(define-language FREEZE
    ; FIGURE 4
    ; TODO: define 'reg'
    (stmt ::= (reg = inst) (br op, label, label) (store op, op))

    (inst ::= (binop attr op, op) (conv op)(bitcast op) (select op, op, op) (icmp cond, op, op) (phi ty, (op, label) ...) 
    (freeze op) (getelementptr op, op ..., op) (load op) (extractelement op, constant) (insertelement op, op, constant))

    (cond ::= eq ne ugt uge slt sle)

    (ty ::= (i natural) (ptr ty) ((i natural) ...) ((ptr ty) ...))

    (binop ::= add udiv sdiv shl and or)

    (attr ::= nsw nuw exact)

    (op ::= Name constant poison)

    (conv ::= zext sext trunc)
    


    ; SECTION 4.2
    ( ::= )

    ( ::= )

    ( ::= )

    (Mem ::= )

    (Name ::= ,(string-append "%" (term variable-not-otherwise-mentioned)))

    (Reg ::= (Name, (ty, v) ...) ...)


    

    
)

; Num checks whether x ∈ Num(size)
; TODO: size <= 32

(define-metafunction FREEZE
    Num : natural natural -> boolean  
    [(Num 0 x) (raise "bitwidth cannot be 0")]
    ;; CHECK OF WHETHER SIZE FITS WITHIN 32/64 BITS
    [(Num size x) true
     (side-condition ,(< (term i) (expt 2 (term size))))
    ]
    [else (false)]
)
