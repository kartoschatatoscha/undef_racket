#include <stdint.h>
#include <stdbool.h>

extern void foo();
extern void bar();

int func(bool c, bool c2){
    while(c){
        if(c2){foo();}
        else {bar();}
    }
    return 1;

}