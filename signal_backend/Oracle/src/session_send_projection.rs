//! PUBLIC fixture bridge for selected established no-chunk sending only.
use crate::{storage,pqr};use prost::Message;
fn u32be(b:&[u8])->u32{u32::from_be_bytes(b.try_into().unwrap())}
pub fn apply(record:&storage::RecordStructure,result:&[u8])->Result<storage::RecordStructure,&'static str>{
 if result.len()<81{return Err("sender prefix width")}
 if result[0]==0{return Ok(record.clone())}if result[0]!=255{return Err("sender status")}
 let mut out=record.clone();let current=out.current_session.as_mut().ok_or("no current")?;
 let chain=current.sender_chain.as_mut().ok_or("no sender")?;if !chain.message_keys.is_empty(){return Err("sender skipped keys unsupported")}
 let key=chain.chain_key.as_mut().ok_or("no sender key")?;key.key=result[1..33].to_vec();key.index=u32be(&result[33..37]);
 let mut pq=pqr::PqRatchetState::decode(current.pq_ratchet_state.as_slice()).map_err(|_|"PQ decode")?;
 let chain=pq.chain.as_mut().ok_or("PQ chain")?;if chain.links.len()!=1{return Err("PQ history unsupported")}
 let key=chain.links[0].send.as_mut().ok_or("PQ send")?;if !key.prev.is_empty(){return Err("PQ skipped keys unsupported")}
 key.next=result[37..69].to_vec();key.ctr=u32be(&result[69..73]);current.pq_ratchet_state=pq.encode_to_vec();
 let management=out.session_management_state.get_or_insert_with(||storage::record_structure::SessionManagementState::Tahini(Default::default()));
 match management{storage::record_structure::SessionManagementState::Tahini(t)=>{
  if t.last_act==storage::tahini_session_management_state::LastAct::ReceiveInactive as i32{t.direction_change_ctr=t.direction_change_ctr.checked_add(1).ok_or("direction counter overflow")?;}
  t.last_act=storage::tahini_session_management_state::LastAct::Send as i32;
 }}Ok(out)
}
