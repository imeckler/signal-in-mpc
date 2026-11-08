// Public, bounded-memory metric scanner. Not an execution/validation replacement.
#include <cstdio>
#include <cstdint>
#include <vector>
#include <string>
#include <stdexcept>
#include <unordered_map>
#include <algorithm>
#include <iostream>
#include <array>
struct Reader {
 FILE* file;int next;
 explicit Reader(const char* path):file(fopen(path,"rb")){if(!file)throw std::runtime_error("open");next=fgetc(file);}
 ~Reader(){fclose(file);}
 void advance(){next=fgetc(file);}
 void space(){while(next==' '||next=='\n'||next=='\r'||next=='\t')advance();}
 void expect(int c){space();if(next!=c)throw std::runtime_error("syntax");advance();}
 uint32_t number(){space();if(next<'0'||next>'9')throw std::runtime_error("number");uint64_t x=0;while(next>='0'&&next<='9'){x=10*x+next-'0';if(x>UINT32_MAX)throw std::runtime_error("overflow");advance();}return x;}
 void seek(const std::string& token){size_t pos=0;while(next!=EOF){int c=next;advance();if(c==token[pos]){if(++pos==token.size())return;}else pos=c==token[0]?1:0;}throw std::runtime_error("missing array");}
 template<class F>void array(F f){expect('[');space();while(next!=']'){expect('[');std::vector<uint32_t> row;space();while(next!=']'){row.push_back(number());space();if(next!=']')expect(',');}expect(']');f(row);space();if(next!=']')expect(',');}expect(']');}
};
struct Dag {
 std::vector<uint32_t> left,right,outputs;std::vector<uint8_t> flags;
 void read(Reader& r){
  r.seek("\"nodes\"");r.expect(':');r.array([&](const auto& row){
   uint32_t l=0,rr=0;uint8_t flag;
   if(row.size()==1&&row[0]==0)flag=0;
   else if(row.size()==4&&row[0]==1)flag=1;
   else if(row.size()==5&&row[0]==2&&row[1]<flags.size()&&row[3]<flags.size()&&row[2]<2&&row[4]<2){flag=2|(row[2]<<2)|(row[4]<<3);l=row[1];rr=row[3];}
   else throw std::runtime_error("node");
   left.push_back(l);right.push_back(rr);flags.push_back(flag);
  });
  r.seek("\"outputs\"");r.expect(':');r.array([&](const auto& row){if(row.size()!=2||row[0]>=flags.size()||row[1]>1)throw std::runtime_error("output");outputs.push_back(row[0]);});
 }
 bool xor_sources(uint32_t i,uint32_t& a,uint32_t& b)const{
  if(flags[i]!=14)return false;auto l=left[i],r=right[i];
  if((flags[l]&3)!=2||(flags[r]&3)!=2)return false;
  auto li=(flags[l]>>2)&1,ri=(flags[l]>>3)&1,lj=(flags[r]>>2)&1,rj=(flags[r]>>3)&1;
  if((left[l]==left[r]&&right[l]==right[r]&&li!=lj&&ri!=rj)||(left[l]==right[r]&&right[l]==left[r]&&li!=rj&&ri!=lj)){a=left[l];b=right[l];return true;}return false;
 }
 void report(bool trace=false){
  std::vector<uint8_t> kinds(flags.size());auto pending=outputs;
  while(!pending.empty()){auto i=pending.back();pending.pop_back();if(kinds[i])continue;uint32_t a,b;bool x=xor_sources(i,a,b);kinds[i]=x?2:1;if(x){pending.push_back(a);pending.push_back(b);}else if((flags[i]&3)==2){pending.push_back(left[i]);pending.push_back(right[i]);}}
  std::vector<uint32_t> depth(flags.size()),local(flags.size());std::unordered_map<uint64_t,uint64_t> groups;
  uint64_t raw_and=0,and_count=0,xor_count=0,unreachable=0;uint32_t max_depth=0,max_local=0,goal=0;
  for(size_t i=0;i<flags.size();++i){raw_and+=(flags[i]&3)==2;if(!kinds[i]){++unreachable;continue;}if((flags[i]&3)!=2)continue;
   uint32_t a=left[i],b=right[i];if(kinds[i]==2)xor_sources(i,a,b);
   auto d=std::max(depth[a],depth[b]);if(kinds[i]==1){depth[i]=d+1;++and_count;}else{depth[i]=d;local[i]=1+std::max(depth[a]==d?local[a]:0,depth[b]==d?local[b]:0);++xor_count;}
   if(depth[i]>max_depth){max_depth=depth[i];goal=i;}max_local=std::max(max_local,local[i]);
   ++groups[(uint64_t(depth[i])<<32)|(uint64_t(local[i])<<2)|kinds[i]];
  }
  uint64_t and_batches=0,xor_batches=0,and_groups=0,xor_groups=0;
  for(auto [key,n]:groups)if((key&3)==1){and_batches+=(n+63)/64;++and_groups;}else{xor_batches+=(n+63)/64;++xor_groups;}
  std::cout<<"{\"nodes\":"<<flags.size()<<",\"raw_and_gates\":"<<raw_and<<",\"executed_and_gates\":"<<and_count<<",\"executed_xor_gates\":"<<xor_count<<",\"unreachable_nodes\":"<<unreachable<<",\"and_depth\":"<<max_depth<<",\"maximum_local_xor_depth\":"<<max_local<<",\"and_groups\":"<<and_groups<<",\"xor_groups\":"<<xor_groups<<",\"packed_and_batches64\":"<<and_batches<<",\"packed_xor_batches64\":"<<xor_batches;
  if(trace){
   std::array<uint64_t,10> path_bins{},and_bins{},bin_depth{};std::array<uint64_t,6> gaps{};uint64_t path_ands=0,path_xors=0;
   for(size_t i=0;i<flags.size();++i)if(kinds[i]&&(flags[i]&3)==2){auto bin=std::min<size_t>(9,i*10/flags.size());if(kinds[i]==1)++and_bins[bin];bin_depth[bin]=std::max<uint64_t>(bin_depth[bin],depth[i]);}
   uint32_t i=goal;
   while((flags[i]&3)==2){uint32_t a=left[i],b=right[i];if(kinds[i]==2){xor_sources(i,a,b);++path_xors;}else{++path_ands;++path_bins[std::min<size_t>(9,uint64_t(i)*10/flags.size())];uint32_t gap=depth[a]>depth[b]?depth[a]-depth[b]:depth[b]-depth[a];++gaps[gap==0?0:gap==1?1:gap<8?2:gap<64?3:gap<1024?4:5];}i=depth[a]>depth[b]?a:depth[b]>depth[a]?b:local[a]>=local[b]?a:b;}
   if(path_ands!=max_depth)throw std::runtime_error("critical path consistency");
   auto output_array=[&](const char* name,const auto& array){std::cout<<",\""<<name<<"\":[";bool first=true;for(auto n:array){if(!first)std::cout<<',';first=false;std::cout<<n;}std::cout<<']';};
   std::cout<<",\"critical_goal_node\":"<<goal<<",\"critical_path_ands\":"<<path_ands<<",\"critical_path_xors\":"<<path_xors;
   output_array("critical_path_and_node_deciles",path_bins);output_array("executed_and_node_deciles",and_bins);output_array("maximum_and_depth_node_deciles",bin_depth);output_array("critical_and_input_depth_gap_bins",gaps);
  }
  std::cout<<"}\n";
 }
};
int main(int argc,char**argv){try{if(argc!=2&&argc!=3)return 2;Reader r(argv[1]);Dag d;d.read(r);d.report(argc==3);return 0;}catch(...){std::cerr<<"public AIG scan failed\n";return 1;}}
