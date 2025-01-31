#!/usr/bin/env python

import graphviz
import json
import os
import re
import sys
import tempfile

DUMP_INTERMEDIATE = False

BG_COLOR = "#222222"
FG_COLOR = "#dddddd"

class ASTNode(dict):
    def __init__(self, **kwargs):
        super().__init__(self, **kwargs)

    def with_index(self, index):
        self.update(index=index)
        return self

class AST:
    def ng_serialize(self, script):
        index = script.get("StatementIndex")
        node = self.ng_inst(script, index)
        node.update(index=index)
        if self.last_index is not None:
            # Link with last node
            self.link_list.append((self.last_index, index))
        if node.get("no_flow", False):
            # Unconditional jump or return node, exec doesn't continue
            self.last_index = None
        else:
            # Non-jump node, assume exec flows linearly
            self.last_index = index
        #print(f"Serialized {node.get("inst")} at {index}")
        return index, node.with_index(index)

    def ng_base(self, **kwargs):
        return ASTNode(**kwargs)

    def ng_basekind(self, kind, **kwargs):
        return self.ng_base(**({"kind": kind} | kwargs))

    def ng_baseinst(self, inst, kind, **kwargs):
        return self.ng_base(**{"inst": inst, "kind": kind} | kwargs)

    def ng_const(self, inst, kind, value):
        return self.ng_baseinst(inst, kind, value=value)

    def ng_const_bool(self, inst, value):
        bval = "true" if value else "false"
        return self.ng_const(inst, "bool", bval)

    def ng_const_num(self, inst, kind, value):
        return self.ng_const(inst, kind, value)

    def ng_const_struct(self, inst, kind, value):
        return self.ng_const(inst, kind, value)

    def ng_let(self, inst, kind, var, expr):
        return self.ng_baseinst(inst, kind, var=self.ng_inst(var), expr=self.ng_inst(expr))

    def ng_prop(self, prop):
        match prop:
            case {"Name": name, "Type": type}:
                return dict(name=name, type=type)
            case _:
                raise ValueError(prop)

    def _ng_propbase(self, propbase):
        match propbase:
            case {"Property": prop}:
                return self.ng_prop(prop)
            case {"Owner": owner, "Property": prop}:
                return self.ng_base(owner=self.ng_objref(owner), prop=self.ng_prop(prop))
            case {"Path": path, "ResolvedOwner": owner}:
                return dict(name=path, owner=self.ng_objref(owner))
            case _:
                raise ValueError(propbase)

    def ng_propkind(self, kind, prop):
        return self.ng_basekind(kind, **self._ng_propbase(prop))

    def ng_propinst(self, inst, kind, prop):
        return self.ng_baseinst(inst, kind, **self._ng_propbase(prop))

    def ng_objref(self, obj):
        match obj:
            case {"ObjectName": objname, "ObjectPath": objpath}:
                fm = re.match("(.*)'(.*):(.*)'", objname)
                if fm is not None:
                    uetype, outer, name = fm.group(1, 2, 3)
                    return self.ng_base(uetype=uetype, outer=outer, name=name, objpath=self.ng_shortpath(objpath))
                sm = re.match("(.*)'(.*)'", objname)
                if sm is not None:
                    uetype, name = sm.group(1, 2)
                    return self.ng_base(uetype=uetype, name=name, objpath=self.ng_shortpath(objpath))
                raise ValueError(obj)
            case str():
                return self.ng_base(uetype="LocalVirtualFunction", name=obj)
            case _:
                raise ValueError(obj)

    def ng_func(self, inst, kind, func, params, **kwargs):
        return self.ng_baseinst(inst, kind, func=self.ng_objref(func), params=[self.ng_inst(p) for p in params], **kwargs)

    def ng_ctxinst(self, inst, kind, obj_expr, offset, rvalue_ptr, ctx_expr):
        rvalue = self.ng_propkind("rvalue ptr", rvalue_ptr) if rvalue_ptr else "null"
        return self.ng_baseinst(inst, kind, obj_expr=self.ng_inst(obj_expr), offset=offset, rvalue_ptr=rvalue, ctx_expr=self.ng_inst(ctx_expr))

    def ng_swcase(self, c):
        match c:
            case {"CaseIndexValueTerm": case_index, "NextOffset": next_offset, "CaseTerm": case_term}:
                return self.ng_base(case_index=self.ng_inst(case_index), next_offset=next_offset, case_term=self.ng_inst(case_term))
            case _:
                raise ValueError(c)

    def ng_switch(self, inst, kind, sw_index, end_goto, cases, default):
        return self.ng_baseinst(inst, kind, sw_index=self.ng_inst(sw_index), end_goto=end_goto, cases=[self.ng_swcase(c) for c in cases], default=self.ng_inst(default))

    def ng_shortpath(self, objpath):
        ridx = objpath.rfind("/") + 1
        return objpath[ridx:]

    def ng_arrconst(self, inst, kind, inner_prop, values):
        return self.ng_baseinst(inst, kind, inner_prop=self.ng_propkind("inner prop", inner_prop), values=[self.ng_inst(v) for v in values]) # TODO: revise values

    def ng_bitfieldconst(self, inst, kind, inner_prop, const_value):
        return self.ng_baseinst(inst, kind, inner_prop=self.ng_propkind("inner prop", inner_prop), const_value=const_value) # TODO: revise const_value

    def ng_inst(self, script, index=None):
        inst = script.get("Inst")
        match script:
            case {"Inst": "EX_SwitchValue", "IndexTerm": sw_index, "EndGotoOffset": end_goto, "Cases": cases, "DefaultTerm": default}:
                return self.ng_switch(inst, "switch value", sw_index, end_goto, cases, default)
            case {"Inst": "EX_Context", "ObjectExpression": obj_expr, "Offset": offset, "RValuePointer": rvalue_ptr, "ContextExpression": ctx_expr}:
                return self.ng_ctxinst(inst, "ctx", obj_expr, offset, rvalue_ptr, ctx_expr)
            case {"Inst": "EX_ClassContext", "ObjectExpression": obj_expr, "Offset": offset, "RValuePointer": rvalue_ptr, "ContextExpression": ctx_expr}:
                return self.ng_ctxinst(inst, "class ctx", obj_expr, offset, rvalue_ptr, ctx_expr)
            case {"Inst": "EX_InterfaceContext", "InterfaceValue": intf_value}:
                return self.ng_baseinst(inst, "intf ctx", intf_value=intf_value)
            case {"Inst": "EX_ByteConst", "Value": value}:
                return self.ng_const_num(inst, "byte", value)
            case {"Inst": "EX_IntConst", "Value": value}:
                return self.ng_const_num(inst, "int", value)
            case {"Inst": "EX_SkipOffsetConst", "Value": value}:
                return self.ng_const_num(inst, "skip offset", value)
            case {"Inst": "EX_FloatConst", "Value": value}:
                return self.ng_const_num(inst, "float", value)
            case {"Inst": "EX_DoubleConst", "Value": value}:
                return self.ng_const_num(inst, "double", value)
            case {"Inst": "EX_StringConst", "Value": value}:
                return self.ng_const(inst, "str", value)
            case {"Inst": "EX_TextConst", "Value": value}:
                return self.ng_const(inst, "text", value)
            case {"Inst": "EX_NameConst", "Value": value}:
                return self.ng_const(inst, "name", value)
            case {"Inst": "EX_VectorConst", "Value": value}:
                return self.ng_const_struct(inst, "const vec", value)
            case {"Inst": "EX_RotationConst", "Value": value}:
                return self.ng_const_struct(inst, "const rot", value)
            case {"Inst": "EX_TransformConst", "Value": value}:
                return self.ng_const_struct(inst, "const trans", value)
            case {"Inst": "EX_SoftObjectConst", "Value": value}:
                return self.ng_const(inst, "soft obj", self.ng_inst(value))
            case {"Inst": "EX_ObjectConst", "Value": value}:
                return self.ng_const(inst, "obj", self.ng_objref(value))
            case {"Inst": "EX_ArrayConst", "InnerProperty": inner_prop, "Values": values}:
                return self.ng_arrconst(inst, "arr const", inner_prop, values)
            case {"Inst": "EX_BitFieldConst", "InnerProperty": inner_prop, "ConstValue": const_value}:
                return self.ng_bitfieldconst(inst, "bitfld const", inner_prop, const_value)
            case {"Inst": "EX_IntZero"}:
                return self.ng_const_num(inst, "int", 0)
            case {"Inst": "EX_IntOne"}:
                return self.ng_const_num(inst, "int", 1)
            case {"Inst": "EX_True"}:
                return self.ng_const_bool(inst, True)
            case {"Inst": "EX_False"}:
                return self.ng_const_bool(inst, False)
            case {"Inst": "EX_Self"}:
                return self.ng_const(inst, "self", "<Self>")
            case {"Inst": "EX_NoObject"}:
                return self.ng_const(inst, "no obj", "<None>")
            case {"Inst": "EX_NoInterface"}:
                return self.ng_const(inst, "no intf", "<None>")
            case {"Inst": "EX_Nothing"}:
                return self.ng_baseinst(inst, "void")
            case {"Inst": "EX_StructConst", "Struct": struct, "Properties": params}:
                return self.ng_func(inst, "struct const", struct, params)
            case {"Inst": "EX_CallMath", "Function": function, "Parameters": params}:
                return self.ng_func(inst, "call math", function, params)
            case {"Inst": "EX_CallMulticastDelegate", "FunctionName": function, "Delegate": delegate, "Parameters": params}:
                return self.ng_func(inst, "call multi dele", function, params, delegate=self.ng_inst(delegate))
            case {"Inst": "EX_FinalFunction", "Function": function, "Parameters": params}:
                return self.ng_func(inst, "final func", function, params)
            case {"Inst": "EX_LocalFinalFunction", "Function": function, "Parameters": params}:
                return self.ng_func(inst, "local final func", function, params)
            case {"Inst": "EX_VirtualFunction", "Function": function, "Parameters": params}:
                return self.ng_func(inst, "virt func", function, params)
            case {"Inst": "EX_LocalVirtualFunction", "Function": function, "Parameters": params}:
                return self.ng_func(inst, "local virt func", function, params)
            case {"Inst": "EX_Let", "Variable": variable, "Expression": expression}:
                return self.ng_let(inst, "let", variable, expression)
            case {"Inst": "EX_LetBool", "Variable": variable, "Expression": expression}:
                return self.ng_let(inst, "let bool", variable, expression)
            case {"Inst": "EX_LetObj", "Variable": variable, "Expression": expression}:
                return self.ng_let(inst, "let obj", variable, expression)
            case {"Inst": "EX_LetWeakObjPtr", "Variable": variable, "Expression": expression}:
                return self.ng_let(inst, "let weak obj ptr", variable, expression)
            case {"Inst": "EX_LetValueOnPersistentFrame", "DestinationProperty": dest_prop, "AssignmentExpression": expression}:
                return self.ng_baseinst(inst, "let val on p.f.", var=self.ng_propkind("val on p.f.", dest_prop), expr=self.ng_inst(expression))
            case {"Inst": "EX_StructMemberContext", "Property": prop, "StructExpression": expression}:
                return self.ng_baseinst(inst, "struct mmb ctx", var=self.ng_propkind("struct mmb", prop), expr=self.ng_inst(expression))
            case {"Inst": "EX_SetArray", "AssigningProperty": prop, "Elements": elements}:
                return self.ng_baseinst(inst, "set array", prop=self.ng_inst(prop), elements=[self.ng_inst(e) for e in elements])
            case {"Inst": "EX_Cast", "Target": target, "ConversionType": conv_type}:
                return self.ng_baseinst(inst, "cast", target=self.ng_inst(target), conv_type=conv_type)
            case {"Inst": "EX_DynamicCast", "Target": target, "Class": clazz}:
                return self.ng_baseinst(inst, "dyn cast class", target=self.ng_inst(target), clazz=self.ng_objref(clazz))
            case {"Inst": "EX_DynamicCast", "Target": target, "InterfaceClass": clazz}:
                return self.ng_baseinst(inst, "dyn cast intf class", target=self.ng_inst(target), clazz=self.ng_objref(clazz))
            case {"Inst": "EX_ObjToInterfaceCast", "Target": target, "InterfaceClass": clazz}:
                return self.ng_baseinst(inst, "obj to intf cast", target=self.ng_inst(target), clazz=self.ng_objref(clazz))
            case {"Inst": "EX_InstanceVariable", "Variable": variable}:
                return self.ng_propinst(inst, "instance var", variable)
            case {"Inst": "EX_LocalVariable", "Variable": variable}:
                return self.ng_propinst(inst, "local var", variable)
            case {"Inst": "EX_LocalOutVariable", "Variable": variable}:
                return self.ng_propinst(inst, "local out var", variable)
            case {"Inst": "EX_DefaultVariable", "Variable": variable}:
                return self.ng_propinst(inst, "def var", variable)
            case {"Inst": "EX_ComputedJump", "OffsetExpression": expression}:
                # Looks like computed jumps only exist in the ExecuteUbergraph, and only one of them exists.
                assert not self.is_ubergraph, "Found multiple computed jumps???"
                self.is_ubergraph = True
                self.cmptd_jump_index = index
                # We cannot generate a meaningful graph for the entire ubergraph
                self.not_entrypoints.add(0)
                return self.ng_baseinst(inst, "computed jump", expr=self.ng_inst(expression), no_flow=True)
            case {"Inst": "EX_Return", "Expression": expression}:
                return self.ng_baseinst(inst, "return", expr=self.ng_inst(expression))
            case {"Inst": "EX_BindDelegate", "FunctionName": func_name, "Delegate": delegate, "ObjectTerm": obj_term}:
                return self.ng_baseinst(inst, "bind dele", func=self.ng_objref(func_name), delegate=self.ng_inst(delegate), obj_term=self.ng_inst(obj_term))
            case {"Inst": "EX_AddMulticastDelegate", "MulticastDelegate": multi_dele, "Delegate": delegate}:
                return self.ng_baseinst(inst, "add multi dele", multi_dele=self.ng_inst(multi_dele), delegate=self.ng_inst(delegate))
            case {"Inst": "EX_RemoveMulticastDelegate", "MulticastDelegate": multi_dele, "Delegate": delegate}:
                return self.ng_baseinst(inst, "remove multi dele", multi_dele=self.ng_inst(multi_dele), delegate=self.ng_inst(delegate))
            case {"Inst": "EX_Jump", "CodeOffset": jmp_offset, "ObjectPath": objpath}:
                self.link_list.append((index, jmp_offset))
                return self.ng_baseinst(inst, "jump", jmp_offset=jmp_offset, objpath=self.ng_shortpath(objpath), no_flow=True)
            case {"Inst": "EX_JumpIfNot", "CodeOffset": jmp_offset, "ObjectPath": objpath, "BooleanExpression": predicate}:
                self.link_list.append((index, jmp_offset))
                return self.ng_baseinst(inst, "jump if not", jmp_offset=jmp_offset, objpath=self.ng_shortpath(objpath), predicate=self.ng_inst(predicate))
            case {"Inst": "EX_PushExecutionFlow", "PushingAddress": push_addr, "ObjectPath": objpath}:
                self.not_entrypoints.add(push_addr)
                return self.ng_baseinst(inst, "push exec", push_addr=push_addr, objpath=self.ng_shortpath(objpath))
            case {"Inst": "EX_PopExecutionFlow"}:
                return self.ng_baseinst(inst, "pop exec", pop_addr=None, no_flow=True)
            case {"Inst": "EX_PopExecutionFlowIfNot", "BooleanExpression": predicate}:
                return self.ng_baseinst(inst, "pop exec if not", pop_addr=None, predicate=self.ng_inst(predicate))
            case {"Inst": "EX_EndOfScript"}:
                return self.ng_baseinst(inst, "script end", no_flow=True)
            case {"Inst": inst}:
                raise ValueError(script)
            case _:
                raise ValueError(script)

    def __init__(self, name, bytecode):
        self.name = name
        self.is_ubergraph = False
        self.not_entrypoints = set()
        self.cmptd_jump_index = None
        self.index_stack = []
        self.last_index = None
        self.link_list = []
        self.temp_link_list = []
        self.script_nodes = {}
        for p in bytecode:
            k, v = self.ng_serialize(p)
            self.script_nodes[k] = v
        for ep in self.get_entrypoints():
            #print(f"resolving stack for ep={ep}")
            self.ng_resolvestack(ep)
            #print()
        self.link_list.extend(self.temp_link_list)

    def ng_resolvestack(self, ep):
        visited_nodes = {}
        def ng_resolvestack_inner(index, in_stack, last_index):
            #print(f"resolvestack(index={index}, in_stack={in_stack}, last_index={last_index}")
            stack = in_stack.copy()
            links = self.get_out_links(index, ep)
            #print(f"{index} stack: {stack}")
            #print(self.script_nodes[index])
            if self.script_nodes[index]["inst"] == "EX_EndOfScript":
                if not len(links) == 0 or not len(stack) == 0:
                    print(f"Unmatched links: {len(links)}")
                    for l in links:
                        print(f"    {l}")
                    print(f"Remaining stack: {len(stack)}")
                    for s in stack:
                        print(f"    {s}")
                assert len(links) == 0
                stack.clear()
            else:
                assert len(links) > 0 or len(stack) > 0
            if index in visited_nodes:
                return
            visited_nodes[index] = stack
            match self.script_nodes[index]:
                case {"inst": "EX_PushExecutionFlow", "push_addr": in_addr}:
                    #print(f"  {index} push addr {in_addr}")
                    stack.append(int(in_addr))
                case {"inst": ("EX_PopExecutionFlow" | "EX_PopExecutionFlowIfNot") as inst, "pop_addr": in_addr}:
                    is_conditional = inst == "EX_PopExecutionFlowIfNot"
                    assert len(stack) > 0
                    addr = stack[-1]
                    #print(f"  {index} pop{" if" if is_conditional else ""} addr {addr}")
                    if addr != in_addr:
                        #print(links)
                        assert in_addr is None
                        assert len(links) == int(is_conditional)
                        self.script_nodes[index]["pop_addr"] = addr
                        self.temp_link_list.append((index, addr))
                        ng_resolvestack_inner(addr, stack[:-1], index)
            node_stack = self.script_nodes[index].get("stack", None)
            if node_stack is not None:
                node_stack.append(stack)
                self.script_nodes[index].update(stack=node_stack)
            for _, next in links:
                ng_resolvestack_inner(next, stack, index)

        ng_resolvestack_inner(0, [], None)

    def _get_links(self, index, dir):
        return {l for l in self.link_list if l[dir] == index}

    def get_in_links(self, index):
        return self._get_links(index, 1)

    def get_out_links(self, index, jump_target=None):
        links = self._get_links(index, 0)
        # Add an out link for the computed jump in the ubergraphs
        if index == self.cmptd_jump_index and jump_target is not None:
            assert jump_target > index
            links.add((index, jump_target))
        return links

    def get_node(self, index):
        return self.script_nodes.get(index, None)

    def get_entrypoints(self):
        def is_entrypoint(ep):
            return ep not in self.not_entrypoints and len(self.get_in_links(ep)) == 0
        entrypoints = {ep for ep in self.script_nodes.keys() if is_entrypoint(ep)}
        assert self.is_ubergraph or len(entrypoints) == 1
        return entrypoints

    def ng_subgraph(self, ep=0):
        if ep == 0:
            return self.script_nodes.values(), self.link_list
        final_nodes = set()
        final_edges = set()
        local_nodes = {0}
        local_edges = set()
        while len(local_nodes - final_nodes) > 0:
            final_nodes |= local_nodes
            for ln in local_nodes:
                local_edges |= self.get_out_links(ln, ep)
            final_edges |= local_edges
            local_nodes.clear()
            for le in local_edges:
                local_nodes.add(le[1])
            local_edges.clear()
        return [self.get_node(fn) for fn in final_nodes], final_edges

class ScriptGraph(graphviz.Digraph):
    def __init__(self, **kwargs):
        super().__init__(**kwargs)
        #self.engine = "fdp"
        #self.attr(bgcolor=BG_COLOR, charset="UTF-8", overlap="vpsc", compound="true")
        self.attr(bgcolor=BG_COLOR, color=FG_COLOR, fontcolor=FG_COLOR, fontname="Arial", fontsize="12", charset="UTF-8", compound="true")
        self.node_attr.update(shape="box", color=FG_COLOR, fontcolor=FG_COLOR, fontname="Arial", fontsize="12")
        self.edge_attr.update(color=FG_COLOR, fontcolor=FG_COLOR, fontname="Arial", fontsize="12")
        self.last_index = None
        self.curr_index = None
        self.script_stack = []

    def make_label(self, n, prefix):
        if isinstance(n, dict):
            excluded_fields = ["index", "kind"]
            fields = []
            if "index" in n:
                fields.append(f"{{index|{n["index"]}}}")
            return "|".join(fields + [f"{{{k}|{{{self.make_label(v, prefix)}}}}}" for k, v in n.items() if k not in excluded_fields])
        elif isinstance(n, list):
            return "|".join([f"{{{self.make_label(e, prefix)}}}" for e in n])
        else:
            return str(n)

    def draw_node(self, n):
        self.node(str(n["index"]), label=self.make_label(n, ""), shape="record", rankdir="LR")

    def draw_edge(self, tail, head):
        self.edge(str(tail), str(head))

def generate_func_graphs(filename, scriptname, bytecode):
    ast = AST(scriptname, bytecode)
    if DUMP_INTERMEDIATE:
        filedir, _ = os.path.splitext(filename)
        debugfile = os.path.join("graphs", filedir, f"{scriptname}.json")
        os.makedirs(os.path.dirname(debugfile), exist_ok=True)
        with open(debugfile, "w") as f:
            json.dump(ast.script_nodes, f, indent=4)
    graphs = []
    entrypoints = ast.get_entrypoints()
    if ast.is_ubergraph:
        assert ast.cmptd_jump_index is not None
    for ep in entrypoints:
        usename = scriptname if ep == 0 else f"{scriptname}_{ep}"
        g = ScriptGraph(comment=usename, format="png")
        nodes, edges = ast.ng_subgraph(ep)
        for n in nodes:
            g.draw_node(n)
        for (tail, head) in edges:
            g.draw_edge(tail, head)
        graphs.append((usename, g))
    return graphs

def render_graph_file(g, infilename, name):
    filedir, _ = os.path.splitext(infilename)
    svgfile = os.path.join("graphs", filedir, f"{name}.gv")
    g.render(filename=f"{svgfile}", format="svg")

def main(filename):
    data = json.load(open(filename))
    for entry in data:
        match entry:
            case {"Type": "Function", "Name": scriptname, "ScriptBytecode": bytecode}:
                print(f"Found function '{scriptname}'")
                for (funcname, fgraph) in generate_func_graphs(filename, scriptname, bytecode):
                    print(f"Rendering '{funcname}'...")
                    render_graph_file(fgraph, filename, funcname)
            case {"Type": sometype}:
                print(f"Found unknown type '{sometype}'")
            case _:
                print(f"Found Whiskey Tango Foxtrot: {dir(entry).join(", ")}")

def main_dir(dirname):
    for root, _, files in os.walk(os.path.join(".", dirname)):
        for file in files:
            f = os.path.join(root, file)
            log_file_name = f"# PROCESSING '{f}' #"
            log_msg_plate = '#' * len(log_file_name)
            print(log_msg_plate)
            print(log_file_name)
            print(log_msg_plate)
            main(f)
            print()

if __name__ == "__main__":
    if len(sys.argv) > 2 and sys.argv[1] == "-d":
        print(f"Hello {sys.argv[0]}: {sys.argv[1]} {sys.argv[2]}")
        main_dir(sys.argv[2])
        pass
    elif len(sys.argv) > 1:
        print(f"Hello {sys.argv[0]}: {sys.argv[1]}")
        main(sys.argv[1])
    else:
        main("Equip_StunSpear.json")
        #main_dir("Map_Menu_Titan_Update8/")
        #main("BPW_InventorySettings_Jetpack.json")
        #main("SFP_GameWorld.json")
        #main("BP_MusicManager.json")
        #main("BPW_Th3UObjectCounter.json")
