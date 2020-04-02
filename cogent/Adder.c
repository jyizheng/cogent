// This file is generated by Cogent

#include "Adder.h"

static inline t2 add(t1 a1)
{
    u32 r2 = a1.p1;
    u32 r3 = a1.p2;
    u32 r4 = r2 + r3;
    bool_t r5 = (bool_t) {.boolean = r4 < r2};
    bool_t r6 = (bool_t) {.boolean = r4 < r3};
    bool_t r7 = (bool_t) {.boolean = r5.boolean || r6.boolean};
    bool_t r8 = (bool_t) {.boolean = 1U};
    bool_t r9 = (bool_t) {.boolean = r7.boolean == r8.boolean};
    t2 r10;
    
    if (r9.boolean) {
        unit_t r11 = (unit_t) {.dummy = 0};
        t2 r12;
        
        r12 = (t2) {.tag = TAG_ENUM_Error, .Error = r11};
        
        t2 r13 = r12;
        
        r10 = r13;
    } else {
        bool_t r14 = r7;
        t2 r15;
        
        r15 = (t2) {.tag = TAG_ENUM_Success, .Success = r4};
        
        t2 r16 = r15;
        
        r10 = r16;
    }
    
    t2 r17 = r10;
    
    return r17;
}


