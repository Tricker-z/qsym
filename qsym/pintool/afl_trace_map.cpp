#include "afl_trace_map.h"

namespace qsym {

const int kMapSize = 65536;

// static  KNOB<bool> g_opt_context_sensitive(KNOB_MODE_WRITEONCE, "pintool",
//     "context_sensitive", "1", "Generate testcases by awaring of contexts");

namespace {

inline bool isPowerOfTwoOrZero(ADDRINT x) {
  return ((x & (x - 1)) == 0);
}

XXH32_hash_t hashPc(ADDRINT pc, bool taken) {
  // // mimic afl's branch map
  // PIN_LockClient();
  // IMG img = IMG_FindByAddress(pc);
  // PIN_UnlockClient();

  // // hopefully IMG_Id is same for every execution
  // if (!IMG_Valid(img))
  //   LOG_FATAL("invalid image");

  // pc -= IMG_LowAddress(img);

  // UINT32 img_id = IMG_Id(img);
  XXH32_state_t state;
  XXH32_reset(&state, 0); // seed = 0
  XXH32_update(&state, &pc, sizeof(pc));
  // XXH32_update(&state, &img_id, sizeof(img_id));
  XXH32_update(&state, &taken, sizeof(taken));
  return XXH32_digest(&state) % kMapSize;
}

} // namespace

void AflTraceMap::allocMap() {
  trace_map_ = (UINT8*)safeMalloc(kMapSize);
  virgin_map_ = (UINT8*)safeMalloc(kMapSize);
  context_map_ = (UINT8*)safeMalloc(kMapSize);
  memset(virgin_map_, 0, kMapSize);
  // Initialize bitmap for cracking branches
  crack_map_ = (UINT8*)safeMalloc(kMapSize);
  crack_virgin_map_ = (UINT8*)safeMalloc(kMapSize);
  memset(crack_virgin_map_, 0, kMapSize);
}

void AflTraceMap::setDefault() {
  memset(trace_map_, 0, kMapSize);
  memset(context_map_, 0, kMapSize);
}

void AflTraceMap::setDefaultCrack() {
  memset(crack_map_, 0, kMapSize);
}

void AflTraceMap::import(const std::string path) {
  ifstream ifs;
  ifs.open(path, ios::binary);
  if (ifs.fail()) {
    LOG_DEBUG("cannot read a file, so use a default trace map\n");
    setDefault();
    return;
  }
  ifs.read((char*)trace_map_, kMapSize);
  ifs.read((char*)context_map_, kMapSize);
  if (!ifs)
    setDefault();
  ifs.close();
}

void AflTraceMap::importCrack(const std::string crack_path) {
  ifstream ifs;
  ifs.open(crack_path, ios::binary);
  if (ifs.fail()) {
    setDefaultCrack();
    return;
  }
  LOG_DEBUG("concolic execution with specified branches to negate\n");
  ifs.read((char*)crack_map_, kMapSize);
  if (!ifs)
    setDefaultCrack();
  ifs.close();
}

ADDRINT AflTraceMap::getIndex(ADDRINT h) {
  return ((prev_loc_ >> 1) ^ h) % kMapSize;
}

bool AflTraceMap::isInterestingContext(ADDRINT h, ADDRINT bits) {
  // if (!g_opt_context_sensitive.Value())
  //   return false;

  bool interesting = false;

  // only care power of two
  if (!isPowerOfTwoOrZero(bits))
    return false;

  for (auto it = visited_.begin();
      it != visited_.end();
      it++) {
    ADDRINT prev_h = *it;

    // Calculate hash(prev_h || h)
    XXH32_state_t state;
    XXH32_reset(&state, 0);
    XXH32_update(&state, &prev_h, sizeof(prev_h));
    XXH32_update(&state, &h, sizeof(h));

    ADDRINT hash = XXH32_digest(&state) % (kMapSize * CHAR_BIT);
    ADDRINT idx = hash / CHAR_BIT;
    ADDRINT mask = 1 << (hash % CHAR_BIT);

    if ((context_map_[idx] & mask) == 0) {
      context_map_[idx] |= mask;
      interesting = true;
    }
  }

  if (bits == 0)
    visited_.insert(h);

  return interesting;
}

void AflTraceMap::commit() {
  if (!path_.empty()) {
    ofstream ofs;
    ofs.open(path_, ios::binary);
    if (ofs.fail())
      LOG_FATAL("Unable to open a bitmap to commit");
    ofs.write((char*)trace_map_, kMapSize);
    ofs.write((char*)context_map_, kMapSize);
    ofs.close();
  }
}

AflTraceMap::AflTraceMap(const std::string path, const std::string crack_path)
  : path_(path),
    crack_path_(crack_path),
    prev_loc_(0),
    visited_() {
  allocMap();
  if (path.empty())
    setDefault();
  else
    import(path);

  if (crack_path.empty())
    setDefaultCrack();
  else
    importCrack(crack_path);
}

bool AflTraceMap::isInterestingBranch(ADDRINT pc, bool taken) {
  ADDRINT h = hashPc(pc, taken);
  ADDRINT idx = getIndex(h);
  bool new_context = isInterestingContext(h, virgin_map_[idx]);
  bool ret = true;

  virgin_map_[idx]++;

  if ((virgin_map_[idx] | trace_map_[idx]) != trace_map_[idx]) {
    ADDRINT inv_h = hashPc(pc, !taken);
    ADDRINT inv_idx = getIndex(inv_h);

    trace_map_[idx] |= virgin_map_[idx];

    // mark the inverse case, because it's already covered by current testcase
    virgin_map_[inv_idx]++;

    trace_map_[inv_idx] |= virgin_map_[inv_idx];
    commit();

    virgin_map_[inv_idx]--;
    ret = true;
  }
  else if (new_context) {
    ret = true;
    commit();
  }
  else
    ret = false;

  prev_loc_ = h;
  return ret;
}

bool AflTraceMap::isCrackBranch(UINT16 prevLoc, UINT16 succLoc) {

  bool is_crack = false;

  do {
    if (crack_map_[prevLoc] == UINT8_MAX) break;
    crack_virgin_map_[prevLoc]++;

    if (edge_covered_.find(prevLoc) == edge_covered_.end()) 
      edge_covered_[prevLoc] = std::set<UINT16>();

    if (edge_covered_[prevLoc].find(succLoc) == edge_covered_[prevLoc].end()) {
      edge_covered_[prevLoc].insert(succLoc);
      is_crack = true;
      break;
    }

    if ((crack_virgin_map_[prevLoc] | crack_map_[prevLoc]) != crack_map_[prevLoc]) {
      crack_map_[prevLoc] |= crack_virgin_map_[prevLoc];
      is_crack = true;
      break;
    }
  } while (0);

  return is_crack;

}

} // namespace qsym
