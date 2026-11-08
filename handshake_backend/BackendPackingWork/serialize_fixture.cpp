// Public serialization only. No parties, protocol run or share conversion.
#include "Math/Bit.h"
#include "Math/gf2n.h"
#include "Tools/octetStream.h"
#include <cassert>
#include <iostream>
int main(){
    gf2n_long::init_field(128);
    octetStream bits,fields;
    for(int i=0;i<128;++i){Bit value(bool(i&1));value.pack(bits);gf2n_long field(i&1);field.pack(fields);}
    bits.flush_bits();
    assert(bits.get_length()==16&&fields.get_length()==2048);
    for(int i=0;i<128;++i){Bit bit;bit.unpack(bits);gf2n_long field;field.unpack(fields);assert(bit.get_bit(0)==bool(i&1)&&field.get_bit(0)==bool(i&1));}
    std::cout<<"{\"logical_bits\":128,\"Bit_serializer_bytes\":"<<bits.get_length()<<",\"gf2n_long_serializer_bytes\":"<<fields.get_length()<<",\"protocol_execution\":false}\n";
}
