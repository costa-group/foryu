import itertools
import logging

from global_params.types import instr_id_T, dependencies_T, var_id_T, block_id_T, function_name_T, SMS_T
from parser.cfg_instruction import CFGInstruction, build_push_spec, build_pushtag_spec
from greedy.greedy_info import GreedyInfo
import json
from parser.constants import split_block
from enum import Enum, auto
from typing import List, Dict, Tuple, Any, Set, Optional

global tag_idx
tag_idx = 0

global function_tags
function_tags = {}


class JumpTypes(Enum):
    """
    Class to represent the different types of exits associated to a block
    """
    CONDITIONAL = auto()
    UNCONDITIONAL = auto()
    TERMINATED = auto()
    MAIN_EXIT = auto()
    FUNCTION_EXIT = auto()


def include_function_call_tags(ins, out_idx, block_spec):
    global function_tags
    global tag_idx

    in_tag, out_tag = function_tags.get(ins.get_op_name(), (-1, -1))

    if in_tag == -1 and out_tag == -1:
        out_tag = tag_idx
        in_tag = tag_idx + 1
        tag_idx += 2

        function_tags[ins.get_op_name()] = (in_tag, out_tag)

    in_tag_instr = build_pushtag_spec(out_idx, in_tag)
    out_idx += 1

    out_tag_instr = build_pushtag_spec(out_idx, out_tag)

    block_spec["user_instrs"] += [in_tag_instr, out_tag_instr]

    # It adds the out jump label after the arguments of the function
    num_funct_arguments = len(ins.get_in_args())
    block_spec["tgt_ws"] = block_spec["tgt_ws"][:num_funct_arguments] + out_tag_instr["outpt_sk"] + block_spec[
                                                                                                        "tgt_ws"][
                                                                                                    num_funct_arguments:]

    # It adds at top of the stack de input jump label
    block_spec["tgt_ws"] = in_tag_instr["outpt_sk"] + block_spec["tgt_ws"]

    # It adds in variables the new identifier for the in and out jump label
    block_spec["variables"] += in_tag_instr["outpt_sk"] + out_tag_instr["outpt_sk"]

    block_spec["yul_expressions"] += "\n" + ins.get_instruction_representation()

    return block_spec, out_idx


class CFGBlock:
    """
    Class for representing a cfg block
    """
    
    def __init__(self, identifier: block_id_T, instructions: List[CFGInstruction], type_block: str,
                 assignment_dict: Dict[str, str]):
        self.block_id = identifier
        self._instructions = instructions

        # Split instruction is recognized as the last instruction
        # As we don't have information on the function calls, we assign it to None and then
        # identify it once we set the function calls
        self._split_instruction = None

        self._jump_type = type_block
        self._jump_to = None
        self._falls_to = None
        self._condition = None
        self.assignment_dict = assignment_dict
        self.is_function_call = False
        self._comes_from = []
        self.function_calls = set()
        self._previous_type = None

        # Stack elements that must be placed in a specific order in the stack after performing
        self._final_stack_elements: List[str] = self._split_instruction.get_out_args() \
            if self._split_instruction is not None else []

        # Entries corresponds to the predecessors blocks from which the value of a phi function
        # at position i is generated. Hence, all phi functions must define the values in the same order
        self._entries: List[block_id_T] = []

        self._spec: SMS_T = None
        self._greedy_ids: List[instr_id_T] = None

        # Greedy Information that needs to be passed
        self._greedy_info: GreedyInfo = None

        # Set of variables that are computed in the current block
        self._id2var = None

        self.liveness = {}
        self.constancy = []

        self.in_layout_solc = []
        self.out_layout_solc = []

    @property
    def final_stack_elements(self) -> List[str]:
        """
        Stack elements that must be placed in a specific order in the stack after performing the operations
        in the block. It can be either the condition of a JUMPI or when invoking a function just after a sub block
        """
        return self._split_instruction.get_out_args() if self._split_instruction is not None else []

    @property
    def split_instruction(self) -> Optional[CFGInstruction]:
        return self._split_instruction

    @split_instruction.setter
    def split_instruction(self, value: CFGInstruction) -> None:
        self._split_instruction = value

    @property
    def entries(self) -> List[block_id_T]:
        return self._entries

    @entries.setter
    def entries(self, value: List[block_id_T]) -> None:
        self._entries = value

    def get_condition(self) -> Optional[var_id_T]:
        return self._condition

    def set_condition(self, cond: var_id_T) -> None:
        self._condition = cond

    def get_block_id(self) -> str:
        return self.block_id

    def set_block_id(self, value: var_id_T) -> None:
        self.block_id = value

    def get_instructions(self) -> List[CFGInstruction]:
        return self._instructions

    def rename_cfg(self, renaming_dict: Dict[var_id_T, var_id_T]) -> None:
        """
        Changes the successors and predecessors according to the renaming dict
        """
        self._jump_to = renaming_dict.get(self._jump_to, self._jump_to)
        self._falls_to = renaming_dict.get(self._falls_to, self._falls_to)
        self._comes_from = [renaming_dict.get(predecessor, predecessor) for predecessor in self._comes_from]
        self._entries = [renaming_dict.get(entry, entry) for entry in self._entries]

    def instructions_without_phi_functions(self) -> List[CFGInstruction]:
        return [instr for instr in self._instructions if instr.get_op_name() != "PhiFunction"]

    def phi_instructions(self) -> List[CFGInstruction]:
        return [instr for instr in self._instructions if instr.get_op_name() == "PhiFunction"]

    def remove_instruction(self, instr_idx: int) -> CFGInstruction:
        """
        Removes the instruction at position instr_index, updating the last split instruction if it affects
        the last instruction
        """

        instr_idx = (len(self._instructions) + instr_idx) % len(self._instructions)
        if instr_idx >= len(self._instructions):
            raise ValueError("Attempting to remove an instruction index out of bounds")
        if instr_idx == len(self._instructions) - 1:
            # There is no split instruction at this point
            self._split_instruction = None

        return self._instructions.pop(instr_idx)

    def insert_instruction(self, index: int, instruction: CFGInstruction) -> None:
        self._instructions.insert(index, instruction)


    def get_liveness(self):
        return self.liveness

    def set_liveness(self, liveness_set: Dict[str,List[str]]):
        self.liveness = liveness_set

    def get_constancy(self):
        return self.constancy

    def set_constancy(self, constancy_list: List[List[Dict]]):
        self.constancy = constancy_list

    def set_in_layout_solc(self, in_layout):
        # Keep the JUNK as is
        self.in_layout_solc = in_layout
                
    def set_out_layout_solc(self, out_layout):
        self.out_layout_solc = out_layout

    def get_in_layout_solc(self):
        return self.in_layout_solc 

    def get_out_layout_solc(self, out_layout):
        return self.out_layout_solc
        
    def get_instructions_to_compute(self) -> List[CFGInstruction]:
        return [instruction for instruction in self._instructions if instruction.must_be_computed()]

    def get_jump_type(self) -> str:
        return self._jump_type

    def get_jump_to(self) -> str:
        return self._jump_to

    def get_falls_to(self) -> str:
        return self._falls_to

    @property
    def successors(self) -> List[block_id_T]:
        return [next_block for next_block in [self._jump_to, self._falls_to] if next_block is not None]

    @property
    def previous_type(self) -> str:
        return self._previous_type

    @previous_type.setter
    def previous_type(self, previous_type: str):
        self._previous_type = previous_type

    def is_function_call(self) -> bool:
        return self.is_function_call

    def set_function_call(self, v) -> None:
        self.is_function_call = v

    def add_comes_from(self, block_id: str) -> None:
        self._comes_from.append(block_id)

    def get_comes_from(self) -> List[str]:
        return self._comes_from

    def set_comes_from(self, new_comes_from: List[str]) -> None:
        self._comes_from = new_comes_from

    def set_jump_type(self, t: str) -> None:
        if t not in ["conditional", "unconditional", "terminal", "falls_to", "sub_block", "mainExit"]:
            raise Exception("Wrong jump type")
        else:
            self._jump_type = t

    def set_jump_to(self, blockId: str) -> None:
        self._jump_to = blockId

    def set_falls_to(self, blockId: str) -> None:
        self._falls_to = blockId

    def set_length(self) -> int:
        return len(self._instructions)

    def insert_jump_instruction(self, tag_value: str) -> None:
        """
        Inserts a JUMP instruction and the corresponding tag
        """
        # Add a PUSH tag instruction
        self._instructions.append(CFGInstruction("PUSH [tag]", [], [tag_value]))

        # Add a JUMP instruction
        jump_instr = CFGInstruction("JUMP", [tag_value], [])
        self._instructions.append(jump_instr)
        self._split_instruction = jump_instr

    def insert_jumpi_instruction(self, tag_value: str) -> None:
        """
        Inserts a JUMPI instruction and the corresponding tag
        """

        assert self._condition is not None, \
            f"Trying to introduce a JUMPI with an empty condition in block {self.block_id}"

        # Add a PUSH tag instruction
        self._instructions.append(CFGInstruction("PUSH [tag]", [], [tag_value]))

        # Add a JUMPI instruction
        jumpi_instr = CFGInstruction("JUMPI", [self._condition, tag_value], [])
        self._instructions.append(jumpi_instr)

        # Finally, assign the JUMPI instruction to the split one
        self._split_instruction = jumpi_instr

    def _process_instructions_from_function_return(self, values: List[var_id_T]):
        """
        Introduces an extra operation representing the application of a return function.
        Hack which guarantees the liveness and layout analysis generate the correct stack
        """
        function_return = CFGInstruction("functionReturn", list(reversed(values)), [])
        self._instructions.append(function_return)
        self._split_instruction = function_return

    def set_jump_info(self, exit_info: Dict[str, Any]) -> None:
        type_block = exit_info["type"]
        if type_block in ["ConditionalJump"]:
            targets = exit_info["targets"]
            self._jump_type = "conditional"
            self._falls_to = targets[0]
            self._jump_to = targets[1]
            self._condition = exit_info["cond"]

        elif type_block in ["Jump"]:
            targets = exit_info["targets"]
            self._jump_type = "unconditional"
            self._jump_to = targets[0]
            # Add to the instructions a JUMP

        elif type_block in ["Terminated"]:
            # We do not store the direction as it generates a loop
            self._jump_type = "terminal"
        elif type_block in [""]:
            # It corresponds to falls_to blocks
            self._jump_type = "falls_to"
        elif type_block in ["MainExit"]:
            self._jump_type = "mainExit"
        elif type_block in ["FunctionReturn"]:
            self._jump_type = "FunctionReturn"
            self._process_instructions_from_function_return(exit_info["returnValues"])

    def process_function_calls(self, function_ids):
        op_names = map(lambda x: x.get_op_name(), self._instructions)
        calls = filter(lambda x: x in function_ids, op_names)
        self.function_calls = set(calls)

        # Finally, we identify the possible split instruction using the now generated information
        if len(self._instructions) > 0 and \
                self._instructions[-1].get_op_name() in itertools.chain(split_block, self.function_calls, ["JUMP","JUMPI"]):
            self._split_instruction = self._instructions[-1]

    @property
    def instructions_to_synthesize(self) -> List[CFGInstruction]:
        if self.split_instruction is not None:
            prefix_instrs = self._instructions[:-1]
        else:
            prefix_instrs = self._instructions

        return [instr for instr in prefix_instrs if instr.get_op_name() != "PhiFunction"]

    @instructions_to_synthesize.setter
    def instructions_to_synthesize(self, value):
        raise NotImplementedError("The instructions for the greedy algorithm cannot be assigned")

    def check_validity_arguments(self):
        """
        It checks for each instruction in the block that there is not
        any previous instruction that uses as input argument the variable
        that is generating as output (there is not aliasing).
        """

        for i in range(len(self._instructions)):
            instr = self._instructions[i]
            out_var = instr.get_out_args()
            if len(out_var) > 0:
                out_var_set = set(out_var)
                pred_inputs = map(lambda x: set(x.get_in_args()).intersection(out_var_set), self._instructions[:i + 1])
                candidates = list(filter(lambda x: x != set(), pred_inputs))
                if len(candidates) != 0:
                    logging.warning("[WARNING]: Aliasing between variables!")


    def translate_opcodes(self, objects_keys, next_idx, object_id, subobjects_idx):
        for ins in self._instructions:
            next_idx = ins.translate_opcode(objects_keys, next_idx, object_id, subobjects_idx)

        return next_idx
    
    def get_stats(self):
        return len(self._instructions)

    
    def get_as_json(self):
        block_json = {}
        block_json["id"] = self.block_id

        instructions_json = []
        for i in self._instructions:
            i_json = i.get_as_json()
            instructions_json.append(i_json)

        block_json["instructions"] = instructions_json

        block_json["exit"] = self.block_id + "Exit"
        block_json["type"] = "BasicBlock"

        jump_block = {}

        if self._jump_type == "conditional":
            jump_block["id"] = self.block_id + "Exit"
            jump_block["instructions"] = []
            jump_block["type"] = "ConditionalJump"
            jump_block["exit"] = [self._falls_to, self._jump_to]
            jump_block["cond"] = self._instructions[-1].get_out_args()

        elif self._jump_type == "unconditional":
            jump_block["id"] = self.block_id + "Exit"
            jump_block["instructions"] = []
            jump_block["type"] = "Jump"
            jump_block["exit"] = [self._jump_to]

        elif self._jump_type == "mainExit":
            jump_block["id"] = self.block_id + "Exit"
            jump_block["instructions"] = []
            jump_block["type"] = "MainExit"
            jump_block["exit"] = [self._jump_to]

        block_json["comes_from"] = self._comes_from
        return block_json, jump_block

    def _get_vars_spec(self, uninter_instructions):
        vars_spec = set()

        for i in uninter_instructions:
            all_vars = i["inpt_sk"] + i["outpt_sk"]
            for a in all_vars:
                vars_spec.add(a)

        return list(vars_spec)

    def _compute_declared_variables(self):
        """
        Returns a dict that links every stack variable to the id of the instruction that
        introduced it
        """
        return {instr["id"]: instr["outpt_sk"] for instr in self._spec["user_instrs"]}

    @property
    def declared_variables(self) -> Set[var_id_T]:
        """
        Variables declared in the block
        """
        if self._id2var is None:
            self._id2var = self._compute_declared_variables()

        # We also need to consider the values defined
        # by the split instruction if any
        if self.split_instruction is not None:
            split_vals = set(self.split_instruction.get_out_args())
        else:
            split_vals = set()

        # We also need to consider values introduced by phi-functions
        return (split_vals.union(out_var for out_var_list in self._id2var.values() for out_var in out_var_list).
                union(phi_function.out_args[0] for phi_function in self.phi_instructions()))

    def out_vars_from_id(self, instr_id: instr_id_T) -> List[var_id_T]:
        """
        Returns the out vars associated to an instruction id.
        Assumes the id belongs to the spec
        """
        if self._id2var is None:
            self._id2var = self._compute_declared_variables()

        return self._id2var.get(instr_id, [])

    def instruction_from_out(self, out_var: var_id_T) -> Optional[CFGInstruction]:
        for instruction in self._instructions:
            out_list = instruction.get_out_args()
            for out_elem in out_list:
                if out_var == out_elem:
                    return instruction
        return None


    def __str__(self):
        s = "BlockID: " + self.block_id + "\n"
        s += "Type: " + self._jump_type + "\n"
        s += "Jump to: " + str(self._jump_to) + "\n"
        s += "Falls to: " + str(self._falls_to) + "\n"
        s += "Comes_from: " + str(self._comes_from) + "\n"
        s += "Instructions: " + str(self._instructions) + "\n"
        return s

    def __repr__(self):
        return json.dumps(self.get_as_json())
