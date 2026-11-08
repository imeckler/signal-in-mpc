// Public representation regression only; does not execute OT or enable Tinier.
#define LONG_BIT_MAC_KEY
#include "GC/ShareSecret.h"
template<class T> class NPartyTripleGenerator;
#include "GC/TinierShare.h"
#include "OT/BitMatrix.hpp"
#include <cassert>
#include <iostream>
int main(){
 gf2n_long::init_field(128);
 const int128 block(0x0123456789abcdefULL,0xfedcba9876543210ULL);
 gf2n_mac_key full(block),legacy(block.get_lower());
 assert(full.get()==block);assert(legacy.get().get_upper()==0);
 assert(full!=legacy);assert(sizeof(full)==16);
 for(unsigned n:{1u,64u,128u,129u,33879u}){
  BitMatrix matrix;matrix.resize_vertical(n);
  for(auto& square:matrix.squares)for(auto& row:square.rows)row=_mm_setzero_si128();
  Slice<BitMatrix> slice(matrix,0,matrix.squares.size());octetStream stream;slice.pack(stream);
  assert(stream.get_length()==((n+127)/128)*2048);
  std::cout<<"AUTH_MATRIX {\"bits\":"<<n<<",\"packed_bytes\":"<<stream.get_length()<<"}\n";
 }
 std::cout<<"public Tinier MAC-width/matrix checks passed\n";
}
