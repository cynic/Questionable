[<RequireQualifiedAccess>]
module UnitTestMarker.MethodCopier
open System
open Data
open Mono.Cecil
open Mono.Cecil.Cil

let private copy_instruction (refInstr : Instruction) (_class : TypeDefinition) : Instruction =
    let _module = _class.Module
    match refInstr.Operand with
    | null -> refInstr
    //| :? FieldReference as defn -> Instruction.Create(refInstr.OpCode, _module.Import(defn))
    | :? TypeReference as defn -> Instruction.Create(refInstr.OpCode, _module.Import(defn))
    | :? MethodReference as defn -> Instruction.Create(refInstr.OpCode, _module.Import(defn))
    | :? FieldReference as defn ->
        let field =
            match _class.Fields |> Seq.tryFind (fun fd -> fd.Name = defn.Name) with
            | Some field -> field
            | None ->
                let refDefn = defn.Resolve()
                let field = FieldDefinition(defn.Name, refDefn.Attributes, _module.Import(defn.FieldType))
                _class.Fields.Add(field)
                field
        Instruction.Create(refInstr.OpCode, field)
    | _ -> refInstr

let setup_method (refM : MethodDefinition) (_class : TypeDefinition) (bodyHandler : ILProcessor -> Instruction -> unit) : MethodDefinition =
    let _module = _class.Module
    let meth = MethodDefinition(refM.Name, MethodAttributes.Public, _module.Import(refM.ReturnType))
    // parameters.
    refM.Parameters |> Seq.iter (fun refParameter ->
        meth.Parameters.Add(ParameterDefinition(refParameter.Name, refParameter.Attributes, _module.Import(refParameter.ParameterType)))
    )
    // local vars
    refM.Body.Variables |> Seq.iter  (fun localVar ->
        meth.Body.Variables.Add(VariableDefinition(localVar.Name,  _module.Import(localVar.VariableType)))
    )
    // stack
    meth.Body.MaxStackSize <- refM.Body.MaxStackSize
    // initLocals?
    meth.Body.InitLocals <- refM.Body.InitLocals
    let il = meth.Body.GetILProcessor()
    refM.Body.Instructions |> Seq.iter (bodyHandler il)
    // exception handlers
    refM.Body.ExceptionHandlers |> Seq.iter (fun handler ->
        let exnH = ExceptionHandler(handler.HandlerType);
        if handler.CatchType <> null then exnH.CatchType <- _module.Import(handler.CatchType)
        exnH.FilterStart <- handler.FilterStart
        exnH.HandlerEnd <- handler.HandlerEnd
        exnH.HandlerStart <- handler.HandlerStart
        exnH.TryEnd <- handler.TryEnd
        exnH.TryStart <- handler.TryStart
        meth.Body.ExceptionHandlers.Add(exnH)
    )
    meth.Resolve()

let private getRefMethod (predicate : MethodDefinition -> bool) (submission : System.IO.FileInfo) : MethodDefinition option =
    let refAsm = AssemblyDefinition.ReadAssembly(submission.FullName)
    let refMethod =
        refAsm.MainModule.GetTypes() |> Seq.tryPick (fun _type ->
            _type.Methods |> Seq.tryFind predicate
        )
    refMethod

// Cecil modifies things in-place, so this gives back a unit.
let private copyMethod (_method : Signature) (submission : System.IO.FileInfo) (_class : TypeDefinition) : unit =
    match getRefMethod (fun (m : MethodDefinition) -> m.Name = _method.Name) submission with
    | None -> ()
    | Some refM ->
        let meth =
            setup_method refM _class (fun il refInstr ->
                let copied = copy_instruction refInstr  _class
                il.Append copied
            )
        _class.Methods.Add meth

//ldarg.0, stfld, newobj
// inspired by https://stackoverflow.com/a/39369989
let copy (methods : Signature list) (submission : UnprocessedSubmission) : Executable =
    let asm =
        let name = submission.CandidateID.Replace(' ', '_')
        let defn = AssemblyNameDefinition(name, Version(1, 0, 0, 0))
        AssemblyDefinition.CreateAssembly(defn, name, ModuleKind.Dll)
    let _module = asm.MainModule
(*
    // assembly references
    AssemblyDefinition.ReadAssembly(submission.Candidate.Executable.FullName).MainModule.AssemblyReferences
    |> Seq.iter (fun asmRef ->
        _module.AssemblyReferences.Add(asmRef)
    )
*)
    let _class = TypeDefinition("Testing", submission.CandidateID, TypeAttributes.Class ||| TypeAttributes.Public, _module.TypeSystem.Object)
    _module.Types.Add _class
    let ctor =
        let attrs =
            MethodAttributes.Public ||| MethodAttributes.HideBySig |||
            MethodAttributes.SpecialName ||| MethodAttributes.RTSpecialName
        let ctor = MethodDefinition(".ctor", attrs, _module.TypeSystem.Void)
        let il = ctor.Body.GetILProcessor()
        [
            il.Create OpCodes.Ldarg_0
            il.Create (OpCodes.Call, _module.Import(typeof<obj>.GetConstructor(System.Type.EmptyTypes))) // call base constructor
        ] |> Seq.iter il.Append
        let getCorrectConstructor (m : MethodDefinition) =
            if m.IsConstructor && not m.HasParameters && m.IsPublic then
                // hm, consider it further...
                let containingClass = m.DeclaringType
                // does this contain at least one of the desired methods?
                methods |> Seq.exists (fun m ->
                    getRefMethod (fun m' -> m.Name = m'.Name && m'.DeclaringType.FullName = containingClass.FullName) submission.Candidate.Executable
                    |> Option.isSome
                )
            else false
        match getRefMethod  getCorrectConstructor submission.Candidate.Executable with
        | None ->
            [ il.Create OpCodes.Nop ; il.Create OpCodes.Ret ] |> Seq.iter il.Append
        | Some refCtor ->
            refCtor.Body.Instructions |> Seq.iter (fun refInstr ->
                if refInstr.OpCode = OpCodes.Ldarg_0 && refInstr.Next.OpCode = OpCodes.Call || refInstr.OpCode = OpCodes.Call then
                    () // ignore.  Otherwise, we end up with a bad stack.
                else
                    let importInstr = copy_instruction refInstr _class
                    il.Append importInstr
            )
        ctor
    _class.Methods.Add ctor
    // duplicate the method...
    methods |> Seq.iter (fun item -> copyMethod item submission.Candidate.Executable _class)
    let filename = sprintf "%s.dll" submission.CandidateID
    if System.IO.File.Exists filename then System.IO.File.Delete filename
    asm.Write (filename)
    { Executable=System.IO.FileInfo(filename); Dependencies=[] }