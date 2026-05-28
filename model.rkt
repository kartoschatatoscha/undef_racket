#lang racket

(require redex/reduction-semantics)
(require rackunit)
(require rebellion/binary/bit)
(require rebellion/binary/bitstring)
(require rebellion/binary/byte)


(define-language FREEZE
  
  ; FIGURE 4
  ; Building blocks
  (var ::= (% string))

  (lbl ::= string)

  (constant len index ::= natural) ; every use needs a check of whether it fits within 16 bits

  (tbit ::= 0 1) ; true bit

  (bit ::= tbit 
       poisonbit)

  (byte ::= (bit bit bit bit bit bit bit bit))

  (bitvector ::= bit ; i1
             (bit bit ...) ; <len x i1> 
             byte ; i8
             (byte byte ...) ; <len x i8> 
             (byte byte) ; i16
             ((byte byte) (byte byte) ...)  ; <len x i16>
  )   


  ; Syntax

  (stmt ::= (var = inst)
        (br label (% lbl)) 
        (br op label (% lbl) label (% lbl))
        (label lbl)
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
        (ret void)
        (ret ty op)
    )

  (cond ::= eq
        ne
        ugt
        uge 
        slt 
        sle)

  (sz ::= 1 8 16)

  (bty ::= (i sz))

  (ty ::= bty 
      (ptr bty)
      (len x bty)
      (ptr (len x bty)))
   ;: TODO retty if needed

  (binop ::= add
         udiv
         sdiv
         shl
         and
         or)

  (attr ::= noattr
        nsw
        nuw
        exact)

  (op ::= var 
      constant 
      poison)

  (bval ::= constant poison)

  (vector ::= (bval ...))

  (val ::= bval vector)

  (retval ::= val void)
  
  (conv ::= zext
        sext
        trunc)
    
  (mem ::= ((index byte) ...))

  (reg ::= ((var (ty val)) ...))

  (p ::= (stmt ...))
  
  )


(define-metafunction FREEZE
  is_valid_ptr : index -> boolean

  [(is_valid_ptr index) (#true)
                        (side-condition (< (term index) (expt 2 16)))]
  [(is_valid_ptr _) (#false)])

    ;; Corresponds to ⟦op⟧_R in the paper

(define-metafunction FREEZE
  lookup_reg_val : reg op -> val
  
  [(lookup_reg_val _ poison) (poison)]

  [(lookup_reg_val _ constant) (constant)]

  [(lookup_reg_val () var) 
   (raise ,(printf "Could not find a variable ~a in the register file" (term var)))] 

  ; Found the bitvector
  [(lookup_reg_val ((var_1 (_ val_1)) (var_2 (_ val_2)) ...) var_1)
   (val_1)]

  ; Non-empty reg, not the correct name
  [(lookup_reg_val (((var_1) (_ val_1)) (var_2 (ty_2 val_2)) ... ) var_3) 
   (lookup_reg_val ((var_2 (ty_2 val_2)) ...) var_3)])


(define-metafunction FREEZE
  lookup_reg_ty : reg op -> ty

  [(lookup_reg_ty _ constant) (i 16)]

  [(lookup_reg_ty () var) 
   (raise ,(printf "Could not find a variable ~a in the register file" (term var)))] 

  ; Found the bitvector
  [(lookup_reg_ty ((var_1 (ty_1 _)) (var_2 (ty_2 _)) ...) var_1)
   (ty_1)]

  ; Name does not match, still looking through reg
  [(lookup_reg_ty (((var_1) (ty_1 _)) (var_2 (ty_2 val_2)) ... ) var_3) 
   (lookup_reg_val ((var_2 (ty_2 val_2)) ...) var_3)])


(define-metafunction FREEZE
  lookup_mem : mem index -> byte 
  
  [(lookup_mem _ index) (raise ,(printf "~a is not a valid pointer" (term index)))
                        (side-condition (not (term (is_valid_ptr index))))]
  
  [(lookup_mem () index) (raise "Value in memory not initialized")
  ]

  ; Found the value in memory

  [(lookup_mem ((index_1 byte_1) (index_2 byte_2) ... ) index_1) (byte_1)] 

  ; Still looking for the value in memory

  [(lookup_mem ((index_1 byte_1) (index_2 byte_2) ... ) index__3) (lookup_mem ((index_2 byte_2) ...) index_3)])


(define-metafunction FREEZE
    type_match : reg op ty -> boolean
    ;; TODO
    [(type_match _ _ _) (#true)]
)

(define-metafunction FREEZE
    overflows : constant (i sz) -> boolean
    ;; TODO
    [(overflows _ _) (#false)]
)

(define-metafunction FREEZE
    has_poison : bitvector -> boolean
    ; function only to be invoked for i1, i8, and i16!

    [(has_poison poisonbit) #true]

    [(has_poison (bit ... poisonbit bit ...)) #true]

    [(has_poison (byte_1 byte_2)) (#true)
     (side-condition (or (term (has_poison byte_1)) (term (has_poison byte_2))))
    ]

    [(has_poison _) #false]
)

(define-metafunction FREEZE
    down_ty : ty val -> bitvector

    [(down_ty (i sz) val) (down_ty_isz (i sz) val)]

    [(down_ty (ptr _) val) (down_ty_isz (i 16) val)]

    ;; TODO for vectors
)
(define-metafunction FREEZE
    up_ty : ty bitvector -> val

    [(up_ty (i sz) val) (up_ty_isz (i sz) val)]

    [(up_ty (ptr _) val) (up_ty_isz (i 16) val)]

    ;; TODO for vectors
)

(define-metafunction FREEZE
    up_ty_isz : ty bitvector -> val

    [(up_ty_isz _ bitvector) (poison)
     (side-condition (term (has_poison bitvector)))
    ]
    
    [(up_ty_isz (i 1) tbit) (tbit)]

    [(up_ty_isz (i 8) byte_1) ,(byte (term byte_1))]

    [(up_ty_isz (i 16) (byte_1 byte_2)) ,(+ (byte (term byte_1)) (byte (term byte_2)))]

)

(define-metafunction FREEZE
    down_ty_isz : (i sz) val -> bitvector

    ;MAYBETODO one can clean up the function by having poison bytes, but that would require to adjust the memory modification function
    [(down_ty_isz (i 1) poison) (poisonbit)]

    [(down_ty_isz (i 8) poison) 
    (poisonbit poisonbit poisonbit poisonbit poisonbit poisonbit poisonbit poisonbit)]

    [(down_ty_isz (i 16) poison) 
    ((poisonbit poisonbit poisonbit poisonbit poisonbit poisonbit poisonbit poisonbit) (poisonbit poisonbit poisonbit poisonbit poisonbit poisonbit poisonbit poisonbit))
    ]
)

(define-metafunction FREEZE
    find_lbl : p lbl -> p

    [(find_lbl () lbl) (raise ,(printf "%s not found" (term lbl)))]

    [(find_lbl ((label lbl) p_rest) lbl) p_rest]

    [(find_lbl (stmt p_rest) lbl) (find_lbl p_rest lbl)]

)
(define-metafunction FREEZE
    start : p -> (p reg mem lbl p) ;; start with main

    [(start p) (start p_entry () () "entry" p)
     (where p_entry (find_lbl p "entry"))
    ]    ;; Memory uninitialized
)

(define-metafunction FREEZE
    end : p reg mem lbl p -> (retty retval)

    [(end () ((var (ty val)) ... ((% "retval") (ty_1 val_1)) ((var_2) (ty_2 val_2))...) _ _ _)
     (ty_1 val_1)
    ] ; % retval is present

    [(end () _ _ _ _) (void void)]
)





(define -->R 
    (reduction-relation FREEZE
    
    ;; Rules in the paper

    ; freeze isz

    [--> (((var = (freeze (i sz) op)) p) reg mem)
     (p ((var ((i sz) ,(random (expt 2 (term sz))))) reg) mem)
     (side-condition (redex-match? FREEZE poison (term (lookup_reg_val reg op))))
    fr_poison]

    [--> (((var = (freeze (i sz) op)) p) reg mem)
     (p ((var ((i sz) (lookup_reg_val reg var))) reg) mem)
     (side-condition (not(redex-match? FREEZE poison (term (lookup_reg_val reg op)))))
     (side-condition (redex-match? FREEZE (term (i sz)) (term (lookup_reg_ty reg var))))
    fr]    

    ;; TODO freeze for vectors

    ;; TODO phi, there needs to be a variable for the last visited label

    [--> (((var = (select op_c ty _ _)) p) reg mem)
     (p ((var (ty poison)) reg) mem)
     (side-condition (redex-match? FREEZE poison (term (lookup_reg_val reg op_c))))
     (side-condition (term (type_match reg op_1 ty)))
     (side-condition (term (type_match reg op_2 ty)))
    sel_poison]

    [--> (((var = (select op_c ty op_1 op_2)) p) reg mem)
     (p ((var (ty (lookup_reg_val reg op_1))) reg) mem)
     (side-condition (redex-match? FREEZE (term 1) (term (lookup_reg_val reg op_c))))
     (side-condition (term (type_match reg op_1 ty)))
     (side-condition (term (type_match reg op_2 ty)))
    sel_1]

    [--> (((var = (select op_c ty op_1 op_2)) p) reg mem)
     (p ((var (ty (lookup_reg_val reg op_2))) reg) mem)
     (side-condition (redex-match? FREEZE (term 0) (term (lookup_reg_val reg op_c))))
     (side-condition (term (type_match reg op_1 ty)))
     (side-condition (term (type_match reg op_2 ty)))
    sel_2]

    ;; TODO and (binop attr ty op op)

    [--> (((var = (and noattr (i sz) op_1 op_2)) p) reg mem)
    (p ((var ((i sz) poison)) reg) mem)

    (side-condition 
        (or 
        (redex-match? FREEZE (term poison) (term (lookup_reg_val reg op_1)))
        (redex-match? FREEZE (term poison) (term (lookup_reg_val reg op_2)))
        )
    )
    (side-condition (term (type_match reg op_1 (i sz))))
    (side-condition (term (type_match reg op_2 (i sz))))
    
    and_poison]
    ; LLVM's and on integers is bitwise-and
    [--> (((var = (and noattr (i sz) op_1 op_2)) p) reg mem)
    (p ((var ((i sz) ,(bitwise-and (term (lookup_reg_val reg op_1)) (term (lookup_reg_val reg op_2))))) reg) mem)
    (side-condition 
        (nor 
        (redex-match? FREEZE (term poison) (term (lookup_reg_val reg op_1)))
        (redex-match? FREEZE (term poison) (term (lookup_reg_val reg op_2)))
        )
    )
    (side-condition (term (type_match reg op_1 (i sz))))
    (side-condition (term (type_match reg op_2 (i sz))))
    and]

    [--> (((var = (add nuw (i sz) op_1 op_2)) p) reg mem)
    (p ((var ((i sz) poison)) reg) mem)

    (side-condition 
        (or 
        (redex-match? FREEZE (term poison) (term (lookup_reg_val reg op_1)))
        (redex-match? FREEZE (term poison) (term (lookup_reg_val reg op_2)))
        )
    )
    (side-condition (term (type_match reg op_1 (i sz))))
    (side-condition (term (type_match reg op_2 (i sz))))
    
    add_nuw_poison]

    [--> (((var = (add nuw (i sz) op_1 op_2)) p) reg mem)
    (p ((var ((i sz) ,(+ (term (lookup_reg_val reg op_1)) (term (lookup_reg_val reg op_2))))) reg) mem)
    (side-condition 
        (nor 
        (redex-match? FREEZE (term poison) (term (lookup_reg_val reg op_1)))
        (redex-match? FREEZE (term poison) (term (lookup_reg_val reg op_2)))
        )
    )
    (side-condition (not (term (overflows ,(+ (term (lookup_reg_val reg op_1)) (term (lookup_reg_val reg op_2))) (i sz)))))
    (side-condition (term (type_match reg op_1 (i sz))))
    (side-condition (term (type_match reg op_2 (i sz))))
    add_nuw]

    [--> (((var = (add nuw (i sz) op_1 op_2)) p) reg mem)
    (p ((var ((i sz) ,(+ (term (lookup_reg_val reg op_1)) (term (lookup_reg_val reg op_2))))) reg) mem)
    (side-condition 
        (nor 
        (redex-match? FREEZE (term poison) (term (lookup_reg_val reg op_1)))
        (redex-match? FREEZE (term poison) (term (lookup_reg_val reg op_2)))
        )
    )
    (side-condition (term (overflows ,(+ (term (lookup_reg_val reg op_1)) (term (lookup_reg_val reg op_2))) (i sz))))
    (side-condition (term (type_match reg op_1 (i sz))))
    (side-condition (term (type_match reg op_2 (i sz))))
    add_nuw_over]

    [--> (((var = (bitcast ty_1 op to ty_2)) p) reg mem)
    (p ((var (ty_2 (up_ty ty_2 (down_ty ty_1 (lookup_reg_val op))))) reg))
    (side-condition (term (type_match reg op ty_1)))
    bitcast]

    ;; TODO load     

    ;; TODO store

    ;; Return
    [--> (((ret void) p_rest) reg mem lbl p)
         (() reg mem lbl p)  ; If there is no retval then the return type is void
    ret_void]

    [--> (((ret ty op) p_rest) reg mem lbl p)
         (() (((% "retval") (ty v)) reg) mem lbl p)
         (where v (lookup_reg_val op))
         (side-condition (term (type_match reg op ty)))
    ret_ty]

    ;; Additional rules
    )

)
