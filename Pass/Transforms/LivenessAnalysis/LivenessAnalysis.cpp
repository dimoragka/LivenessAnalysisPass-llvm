#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/CFG.h"
#include <string>
#include <map>
#include <iostream>
#include <fstream>
#include <set>

using namespace llvm;
using namespace std;

#define DEBUG_TYPE "ValueNumbering"

using namespace llvm;

namespace {
struct LivenessAnalysis : public FunctionPass {
    string func_name = "test";
    static char ID;
    LivenessAnalysis() : FunctionPass(ID) {}

    bool runOnFunction(Function &F) override {
        errs() << "LivenessAnalysisPass: ";
        errs() << F.getName() << "\n";

        if (F.getName() != func_name) return false;

        // Get filename
        const auto fname_with_ext = F.getParent()->getSourceFileName();

        // Remove extension
        size_t dot_index = fname_with_ext.find_last_of(".");
        std::string fname = fname_with_ext.substr(0, dot_index);

        std::map<const BasicBlock *, std::set<const AllocaInst *>> bb_live_out_map;  // LIVEOUT
        std::map<const BasicBlock *, std::set<const AllocaInst *>> bb_uevar_map;     // UEVAR
        std::map<const BasicBlock *, std::set<const AllocaInst *>> bb_kill_map;      // KILL

        //
        // STEP 1: Compute UEVAR and KILL.
        //
        for (const auto &basic_block : F) {

            errs() << "\nBasic block name: " << basic_block.getName() << "\n";
            errs() << "-----------------" << "\n";

            for (const auto &inst : basic_block) {

                errs() << inst << " (number of Operands: " << inst.getNumOperands();

                if (inst.isBinaryOp()) {

                    const auto inst_op_code = inst.getOpcode();

                    // Supported mathematical binary operations
                    if (inst_op_code == Instruction::Add || inst_op_code == Instruction::Mul ||
                        inst_op_code == Instruction::UDiv || inst_op_code == Instruction::SDiv ||
                        inst_op_code == Instruction::Sub) {

                        errs() << " , Op code: " << inst.getOpcodeName() << ")";

                        const auto alloca_insts = getAllocaInstFromBinaryOp(inst);
                        if (alloca_insts.first) {
                            auto &bb_uevar = bb_uevar_map[&basic_block];
                            // Check if it is already killed and if not add it to UEVAR
                            const auto bb_kill = bb_kill_map[&basic_block];
                            const auto bb_kill_it = bb_kill.find(alloca_insts.first);
                            if (bb_kill_it == bb_kill.end()) {
                                bb_uevar.insert(alloca_insts.first);
                            }
                        }
                        if (alloca_insts.second) {
                            auto &bb_uevar = bb_uevar_map[&basic_block];
                            // Check if it is already killed and if not add it to UEVAR
                            const auto bb_kill = bb_kill_map[&basic_block];
                            const auto bb_kill_it = bb_kill.find(alloca_insts.second);
                            if (bb_kill_it == bb_kill.end()) {
                                bb_uevar.insert(alloca_insts.second);
                            }
                        }
                    }
                }

                if (const auto store_inst = dyn_cast_or_null<StoreInst>(&inst)) {
                    //
                    if (const auto alloca_value = dyn_cast_or_null<AllocaInst>(store_inst->getOperand(1))) {
                        auto &bb_kill = bb_kill_map[&basic_block];
                        bb_kill.insert(alloca_value);
                    }
                    //
                    if (const auto load_value = dyn_cast_or_null<LoadInst>(store_inst->getOperand(0))) {
                        const AllocaInst *alloca_inst = dyn_cast_or_null<AllocaInst>(load_value->getOperand(0));
                        auto &bb_uevar = bb_uevar_map[&basic_block];
                        bb_uevar.insert(alloca_inst);
                    }
                }

                if (const auto icm_inst = dyn_cast_or_null<ICmpInst>(&inst)) {
                    //
                    if (const auto load_value = dyn_cast_or_null<LoadInst>(icm_inst->getOperand(1))) {
                        const AllocaInst *alloca_inst = dyn_cast_or_null<AllocaInst>(load_value->getOperand(0));
                        auto &bb_uevar = bb_uevar_map[&basic_block];
                        bb_uevar.insert(alloca_inst);
                    }
                    //
                    if (const auto load_value = dyn_cast_or_null<LoadInst>(icm_inst->getOperand(0))) {
                        const AllocaInst *alloca_inst = dyn_cast_or_null<AllocaInst>(load_value->getOperand(0));
                        auto &bb_uevar = bb_uevar_map[&basic_block];
                        bb_uevar.insert(alloca_inst);
                    }
                }

                errs() << "\n";
            }
        }

        //
        // STEP 2: Basic Iterative Algorithm.
        //
        const auto &bb_list = F.getBasicBlockList();
        bool test = true;
        while(test) {
            test = false;
            for (auto bb_it = bb_list.rbegin(); bb_it != bb_list.rend(); ++bb_it) {
                auto previous_live_out = bb_live_out_map[&(*bb_it)];
                bb_live_out_map[&(*bb_it)].clear();
                auto & new_bb_live_out = bb_live_out_map[&(*bb_it)];
                for (const BasicBlock *succ : successors(&(*bb_it))) {
                    const auto succ_bb_live_out = bb_live_out_map[succ];
                    const auto succ_bb_kill = bb_kill_map[succ];
                    const auto succ_bb_uevar = bb_uevar_map[succ];
                    std::set<const AllocaInst*> diff;
                    std::set_difference(succ_bb_live_out.begin(), succ_bb_live_out.end(),
                            succ_bb_kill.begin(), succ_bb_kill.end(), std::inserter(diff, diff.begin()));
                    std::set_union(diff.begin(), diff.end(), succ_bb_uevar.begin(), succ_bb_uevar.end(),
                            std::inserter(new_bb_live_out, new_bb_live_out.begin()));
                }
                std::set<const AllocaInst*> intersect;
                std::set_difference(new_bb_live_out.begin(), new_bb_live_out.end(),
                                      previous_live_out.begin(), previous_live_out.end(), std::inserter(intersect, intersect.begin()));

                if (!intersect.empty()) {
                    test = true;
                }
            }
        }

        // Print results on terminal.
        errs() << "\nLiveness Analysis Pass (LAP)" << "\n";
        errs() << "==============================" << "\n";
        for (const auto& basic_block : F) {
            errs() << "\nBasic block name: " << basic_block.getName() << "\n";
            errs() << "-----------------" << "\n";
            errs() << "UEVAR: ";
            for (const auto& uevar : bb_uevar_map[&basic_block]) {
                errs() << uevar->getName() << " ";
            }
            errs() << "\nKILL: ";
            for (const auto& killvar : bb_kill_map[&basic_block]) {
                errs() << killvar->getName() << " ";
            }
            errs() << "\nLIVEOUT: ";
            for (const auto& loutvar : bb_live_out_map[&basic_block]) {
                errs() << loutvar->getName() << " ";
            }
            errs() << "\n";
        }
        errs() << "\n";

        // Write results on file.
        output_to_file(F, bb_uevar_map, bb_kill_map, bb_live_out_map, fname);

        return true;
    }

    std::pair<const AllocaInst*, const AllocaInst*> getAllocaInstFromBinaryOp(const Instruction& binary_inst) {

        const auto first_value = binary_inst.getOperand(0);
        const LoadInst *first_load = dyn_cast_or_null<LoadInst>(first_value);
        const AllocaInst *first_alloca = nullptr;
        if (first_load) {
            first_alloca = dyn_cast_or_null<AllocaInst>(first_load->getOperand(0));
        }

        const auto second_value = binary_inst.getOperand(1);
        const LoadInst *second_load = dyn_cast_or_null<LoadInst>(second_value);
        const AllocaInst *second_alloca = nullptr;
        if (second_load) {
            second_alloca = dyn_cast_or_null<AllocaInst>(second_load->getOperand(0));
        }

        return std::make_pair(first_alloca, second_alloca);
    }

    void output_to_file(const Function& F, const std::map<const BasicBlock *, std::set<const AllocaInst *>>& bb_uevar_map,
                        const std::map<const BasicBlock *, std::set<const AllocaInst *>>& bb_kill_map,
                        const std::map<const BasicBlock *, std::set<const AllocaInst *>>& bb_live_out_map,
                        const std::string& filename) {
        ofstream output;
        output.open(filename + ".out");

        output << "\nLiveness Analysis Pass (LAP)" << "\n";
        output << "==============================" << "\n";
        for (const auto& basic_block : F) {
            output << "\nBasic block name: " << std::string(basic_block.getName()) << "\n";
            output << "-----------------" << "\n";
            output << "UEVAR: ";
            for (const auto uevar : bb_uevar_map.at(&basic_block)) {
                output << std::string(uevar->getName()) << " ";
            }
            output << "\nKILL: ";
            for (const auto killvar : bb_kill_map.at(&basic_block)) {
                output << std::string(killvar->getName()) << " ";
            }
            output << "\nLIVEOUT: ";
            for (const auto loutvar : bb_live_out_map.at(&basic_block)) {
                output << std::string(loutvar->getName()) << " ";
            }
            output << "\n";
        }
        output << "\n";
    }

}; // end of struct LivenessAnalysis
}  // end of anonymous namespace

char LivenessAnalysis::ID = 0;
static RegisterPass<LivenessAnalysis> X("LivenessAnalysis", "LivenessAnalysis Pass",
                             false /* Only looks at CFG */,
                             false /* Analysis Pass */);
