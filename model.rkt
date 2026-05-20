#lang racket

(require redex/reduction-semantics)
(require rackunit)


(define-language FREEZE
    ; FIGURE 4
    ; Building blocks
    (var lbl ::= % string)

    (constant len index ::= natural)                ; every use needs a check of whether it fits within 16 bits

    (tbit ::= 0 1) ; true bit

    (bit ::= tbit 
             poisonbit
    )

    (byte ::= (bit bit bit bit bit bit bit bit))

    (bitvector ::= bit 
                   (bit bit ...) 
                   byte 
                   (byte byte ...) 
                   (byte byte) 
                   ((byte byte) (byte byte) ...) 
                   poison
    )   ; Values stored in reg, mem stores only the bytes


    ; Syntax

    (stmt ::= (var = inst)
              (br label lbl) 
              (br op label lbl label lbl)
    )

    (inst ::= (binop attr ty op op)
              (conv ty op to op)
              (bitcast ty op to ty)
              (select op ty op op)
              (icmp cond ty op op)
              (phi ty [op lbl] [op lbl] ...)
              (freeze ty op)
              (getelementptr (ptr ty) op (ty op) (ty op) ...)
              (extractelement (len x bty) op constant)
              (insertelement (len x bty) op constant)
              (load ty (ptr ty) op)
              (store ty op (ptr ty) op)
    )

    (cond ::= eq
              ne
              ugt
              uge 
              slt 
              sle 
    )

    (bty ::= i1 
             i8
             i16
    )

    (ty ::= bty 
            (ptr bty)
            (len x bty)
            (ptr (len x bty))
    )

    (binop ::= add
               udiv
               sdiv
               shl
               and
               or
    )

    (attr ::= noattr
              nsw
              nuw
              exact
    )

    (op ::= var 
            constant 
            poison
    )

    (conv ::= zext
              sext
              trunc
    )
    
    (mem ::= ((index byte) ...))

    (reg ::= ((var (ty bitvector)) ...))  

    
)

(define-metafunction FREEZE
    is_valid_ptr : index -> boolean

    [(is_valid_ptr index) (true)
    (side-condition (< (term index) (expt 2 16)))
    ]
    [(is_valid_ptr _) (false)]
)

(define-metafunction FREEZE
    lookup_reg_val : reg var -> bitvector

    [(lookup_reg_val () var) 
    (raise ,(printf "Could not find a variable ~a in the register file" (term var)))] 

    ; Found the bitvector
    [(lookup_reg_val ((var_1 (ty_1 bitvector_1)) (var_2 (ty_2 bitvector_2)) ...) var_1)
    (bitvector_1)]

    ; Non-empty reg, not the correct name
    [(lookup_reg_val (((var_1) (ty_1 bitvector_1)) (var_2 (ty_2 bitvector_2)) ... ) var_3) 
    (lookup_reg_val ((var_2 (ty_2 bitvector_2)) ...) var_3)
    ]
)

(define-metafunction FREEZE
    lookup_reg_ty : reg var -> ty

    [(lookup_reg_ty () var) 
    (raise ,(printf "Could not find a variable ~a in the register file" (term var)))] 

    ; Found the bitvector
    [(lookup_reg_ty ((var_1 (ty_1 bitvector_1)) (var_2 (ty_2 bitvector_2)) ...) var_1)
    (ty_1)]

    ; Non-empty reg, not the correct name
    [(lookup_reg_ty (((var_1) (ty_1 bitvector_1)) (var_2 (ty_2 bitvector_2)) ... ) var_3) 
    (lookup_reg_val ((var_2 (ty_2 bitvector_2)) ...) var_3)
    ]
)

(define-metafunction FREEZE
    lookup_mem : mem index -> byte 

    [(lookup_mem _ index) (raise ,(printf "~a is not a valid pointer" (term index)))
    (side-condition (term (valid_ptr index)))
    ]
    [(lookup_mem () index) (raise "Value in memory not initialized")
    (side-condition (term (valid_ptr index)))
    ]

    ; Found the value in memory

    [(lookup_mem ((index_1 byte_1) (index_2 byte_2) ... ) index_1) (byte_1)] 

    ; Still looking for the value in memory

    [(lookup_mem ((index_1 byte_1) (index_2 byte_2) ... ) index__3) (lookup_mem ((index_2 byte_2) ...) index_3)]

)




