# Loop Unswitching

### Original 
- Swift code: 
- ```
    while(c){
        if(c2){
            return 2;
        }else{
            return 1;
        }
    }
    return 0;
    ```

- Model code:
- ```
    label "entry"
    (% "c") = add nuw(i 1) 0 0
    (% "c2") = add nuw (i 1) 1 1
    br (% "c") label (% "while") label (% "end")

    label "while"
    br (% "c2") label (% "then") label (% "else")

    label "then"
    ret (i 16) 2

    label "else"
    ret (i 16) 1

    label "end"
    ret (i 16) 0
    ```


### Transformed
- Swift code: 
- ```
    c_fr = freeze(c2);
    if(c_fr){
        while(c){return 2;}
    }else{
        while(c){return 1;}
    }
    return 0;
    ```

- Model code:
- ```
    label "entry"
    (% "c") = add nuw (i 1) 0 0
    (% "c2") = add nuw (i 1) 1 1
    (% "c_fr") = freeze (i 1) (% "c2")
    br label (% "if")

    label "if"
    br (% "c_fr") label (% "then") label (% "else")

    label "then"
    br (% "c") label (% "while_then") label (% "end")

    label "else"
    br (% "c") label (% "while_else") label (% "end")

    label "while_then"
    ret (i 16) 2

    label "while_else"
    ret (i 16) 1

    label "end"
    ret (i 16) 0
    ```


# Reverse predication

### Original
```
label "entry"
(% "c") = (add nuw (i 1) 1 1)
(% "x") = (select (% "c") (i 16) 100 10)
ret (i 16) (% "x")
```

### Transformed
```
label "entry"
(% "c") = (add nuw (i 1) 1 1)
(% "c2") = (freeze (i 1) (% "c"))
br (% "c2") label (% "true") label (% "false")

label "true"
br label (% "merge")

label "false"
br label (% "merge")

label "merge"
(% "x") = (phi (i 16) [100 "true"] [10 "false"])
ret (i 16) (% "x")
```