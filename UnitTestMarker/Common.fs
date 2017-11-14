[<RequireQualifiedAccess>]
module UnitTestMarker.Common
open System.Reflection
open System.Text.RegularExpressions
open System
open System.IO
open Data
open Mono.Cecil
open Mono.Cecil.Cil

let internal asSTA (timeLimit : int option) (f : unit -> 'a) : Either<'a, TimedExecutionError> =
    let result = ref Unchecked.defaultof<'a>
    let failure = ref None
    let t =
        Threading.Thread (fun () -> 
            try
            result := f ()
            with
            | e -> failure := Some e
        )
    t.SetApartmentState Threading.ApartmentState.STA
    t.IsBackground <- true
    t.Start()
    match timeLimit with
    | Some n -> t.Join n |> ignore
    | None -> t.Join ()
    if t.IsAlive && Option.isSome timeLimit then
        try
            t.Abort()
            Error TimeoutExceeded
        with
        | _ -> Error TimeoutExceeded
    else
        //else printfn "Thread finished successfully"
        match !failure with
        | Some e ->
            if e.InnerException <> null then Error (TimedExecutionFailed e.InnerException)
            else raise e // this is an error of the executor, not the wrapped function.
        | None -> OK !result

let internal resolveHandler =
    let cryptoCache : Map<byte[],Assembly> ref = ref Map.empty
    fun (exeInfo : FileInfo) ->
        let resolv (_ : obj) (args : ResolveEventArgs) =
            let frontMatter = args.Name.Split([|','|]) |> Seq.head
            let files = Seq.append (exeInfo.Directory.EnumerateFiles("*.dll")) (exeInfo.Directory.EnumerateFiles("*.exe"))
            match files |> Seq.tryFind (fun x -> Path.GetFileNameWithoutExtension(x.Name).Contains(frontMatter)) with
            | Some fi ->
                //printfn "Arg: %s, found: %s" args.Name fi.FullName
                // if I'm loading it, check if it's in the cryptocache.  If so, just use the existing copy.
                let hash = System.Security.Cryptography.SHA256.Create().ComputeHash(File.ReadAllBytes(fi.FullName))
                match !cryptoCache |> Map.tryFind hash with
                | Some asm -> asm
                | None ->
                    let asm = Assembly.LoadFile(fi.FullName)
                    cryptoCache := Map.add hash asm !cryptoCache
                    asm
            | None ->
                //printfn "Arg: %s, nothing found that matches." args.Name
                null
        new ResolveEventHandler(resolv)

let internal newAppDomain (resolver : ResolveEventHandler) : AppDomain * IDisposable =
    let myAssemblies = Assembly.GetExecutingAssembly().GetReferencedAssemblies()
    let appD =
        let guidStr = Guid.NewGuid().ToString()
        let setup = new AppDomainSetup()
        AppDomain.CreateDomain(guidStr, null, setup)
    appD.add_AssemblyResolve (resolver)
    myAssemblies |> Seq.iter (appD.Load >> ignore)
    let disposer =
        { new IDisposable with
            member __.Dispose () =
                appD.remove_AssemblyResolve (resolver)
                AppDomain.Unload(appD)
        }
    appD, disposer

let internal withExecutable (exe : Executable) (f : Assembly -> Either<'a,'b>) : Either<'a,'b> =
    try
        let handler = resolveHandler exe.Executable
        AppDomain.CurrentDomain.add_AssemblyResolve (handler)
        try
            let asm = Assembly.LoadFile(exe.Executable.FullName)
            f asm
        finally
            AppDomain.CurrentDomain.remove_AssemblyResolve(handler)
    with
    | e -> failwithf "Exception in withExecutable: %s\nStackTrace\n%s" e.Message e.StackTrace

let internal parseType (t : System.Type) : Either<BasicType, TypeError> =
    let rec parseType (t : System.Type) : BasicType =
        if t.Equals (typeof<System.Double>) then Double
        elif t.Equals (typeof<System.Int32>) then Int
        elif t.Equals (typeof<System.Char>) then Char
        elif t.Equals (typeof<System.Boolean>) then Bool
        elif t.Equals (typeof<System.String>) then String
        elif t.IsArray then Array (parseType <| t.GetElementType())
        elif t.GetGenericTypeDefinition().Equals(typedefof<System.Collections.Generic.List<_>>) then
            GenericList (parseType <| t.GetGenericArguments().[0])
        else
            let e = System.Exception()
            e.Data.Add(0, t)
            raise e
    try
        OK (parseType t)
    with
    | e -> Error <| UnsupportedType (e.Data.[0] :?> System.Type)

let internal parseSignature (m : MethodInfo) : Either<Signature, SignatureError> =
    either {
        let! retType = parseType m.ReturnType |> Either.wrapError (TypeError.unwrap >> UnsupportedReturnType)
        let args = m.GetParameters() |> Seq.map (fun pi -> pi.ParameterType) |> Seq.toList
        let rec parseArgs n (args : Type list) accum =
            either {
                match args with
                | [] -> return {ReturnType=retType; Name=m.Name; Parameters=List.rev accum }
                | x::xs ->
                    let! pType = parseType x |> Either.wrapError (TypeError.unwrap >> (fun v -> UnsupportedParameterType (n,v)))
                    yield! parseArgs (n+1) xs (pType :: accum)
            }
        yield! parseArgs 1 args []
    }

let internal getMethod (methodName : string) (asm : Assembly) : Either<MethodInfo,MethodError> =
    let _method =
        asm.GetTypes()
        |> Seq.collect (fun t ->
            t.GetMethods(BindingFlags.Public ||| BindingFlags.NonPublic ||| BindingFlags.Instance ||| BindingFlags.Static)
        ) |> Seq.tryFind (fun m -> m.Name = methodName)
    match _method with
    | Some m -> OK m
    | None -> Error (MethodNotFound methodName)

let internal getInputs (_method : Signature) (exe : Executable) : Either<TestCase list, ReadInputsError> =
    either {
        let testName = sprintf "%s_Tests" _method.Name
        return! withExecutable exe (fun asm ->
            either {
                let! m = getMethod testName asm |> Either.wrapError TestCasesNotFound
                let classType = m.DeclaringType
                let! result =
                    asSTA None (fun () ->
                        let o = Activator.CreateInstance(classType)
                        let retval = m.Invoke(o, null)
                        let enumerable = retval :?> seq<System.Tuple<_[],_>>
                        let result =
                            enumerable |> Seq.map (fun tuple ->
                                let args, expected = tuple.Item1, tuple.Item2
                                let out = BasicValue (_method.ReturnType, expected)
                                let inputs = Seq.zip _method.Parameters args |> Seq.map BasicValue
                                {Arguments=Seq.toList inputs; Expected=out}
                            ) |> Seq.toList
                        result
                    ) |> Either.wrapError TestCaseReadingFailed
                return result
            }
        )
    }

let internal getExecutable (exeInfo : FileInfo) : Executable =
    try
        let handler = resolveHandler exeInfo
        AppDomain.CurrentDomain.add_AssemblyResolve (handler)
        try
            let asm = Assembly.LoadFile(exeInfo.FullName)
            let deps =
                asm.GetReferencedAssemblies()
                |> Seq.choose (fun asmName ->
                    let tmp = Assembly.Load(asmName)
                    if tmp.GlobalAssemblyCache then None
                    else Some <| FileInfo(tmp.Location)
                ) |> Seq.toList
            { Executable=exeInfo; Dependencies=deps }
        finally
            AppDomain.CurrentDomain.remove_AssemblyResolve (handler)
    with
    | e -> failwithf "Exception in getExecutable: %s\nStackTrace\n%s" e.Message e.StackTrace

let internal getMethodDefinition (file : FileInfo) (p : MethodDefinition -> bool) : MethodDefinition option =
    let asm = AssemblyDefinition.ReadAssembly(file.FullName)
    asm.Modules |> Seq.tryPick (fun m -> m.Types |> Seq.tryPick (fun t -> t.Methods |> Seq.tryFind p))

let private getDefault (executable : Executable) (signature : Signature) : Option<Instruction[]> =
    getMethodDefinition executable.Executable (fun m -> m.Name = signature.Name + "_Default")
    |> Option.map (fun m ->
        m.Body.Instructions.ToArray ()
    )

let internal getReference (executable : FileInfo) (markMap : System.Collections.Generic.IDictionary<string,int>) : Either<Reference,ReferenceError> =
    either {
        let executable = getExecutable executable
        let! questions =
            markMap |> Either.map (fun kvp ->
                either {
                    let! m = withExecutable executable (getMethod kvp.Key) |> Either.wrapError ReferenceMethodNotFound
                    let! signature = parseSignature m |> Either.wrapError UnparseableReferenceSignature
                    let! inputs = getInputs signature executable |> Either.wrapError InputsError
                    return {Mark=kvp.Value; Method=signature; Inputs=inputs; DefaultBody=getDefault executable signature}
                }
            )
        return {Executable=executable; Questions = questions}
    }
        
let internal asRegexes (xs : string list) : Either<Regex list, string> =
    try
        xs |> List.map (fun s -> new Regex(s)) |> OK
    with
    | :? ArgumentException as e -> Error e.Message
