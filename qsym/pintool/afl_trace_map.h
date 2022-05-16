#ifndef __AFL_TRACE_MAP_H__
#define __AFL_TRACE_MAP_H__

#define FFL(_b) (0xffULL << ((_b) << 3))
#define FF(_b)  (0xff << ((_b) << 3))

#include <cstring>
#include <fstream>
#include <iostream>
#include <set>
#include <unordered_map>

#include "common.h"

namespace qsym {

class AflTraceMap {

private:
  std::string path_;
  std::string crack_path_;
  ADDRINT prev_loc_;
  UINT8 *trace_map_;
  UINT8 *virgin_map_;
  UINT8 *context_map_;
  UINT8 *crack_map_;
  UINT8 *crack_virgin_map_;
  std::set<ADDRINT> visited_;
  std::unordered_map<UINT16, std::set<UINT16>> edge_covered_; 

  void allocMap();
  void setDefault();
  void setDefaultCrack();
  void import(const std::string path);
  void importCrack(const std::string crack_path);
  void commit();
  ADDRINT getIndex(ADDRINT h);
  bool isInterestingContext(ADDRINT h, ADDRINT bits);

public:
  AflTraceMap(const std::string path, const std::string crack_path);
  bool isInterestingBranch(ADDRINT pc, bool taken);
  bool isCrackBranch(UINT16 prevLoc, UINT16 succLoc);
};
} // namespace qsym
#endif // __AFL_TRACE_MAP_H__