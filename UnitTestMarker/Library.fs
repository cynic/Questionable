namespace UnitTestMarker
open System
open Microsoft.Build.Execution
open System.IO
open Data
open Mono.Cecil
open Mono.Cecil.Cil

(*
The idea here is to have a "reference" executable which contains the appropriate methods that need to be tested.
This executable also contains test inputs and their expected outputs, named by convention:
if a method ABC must be tested, then...
- ABC_Tests gives back test inputs and expected outputs.
- ABC_Default is the default implementation for the method. (this is optional)
*)

[<RequireQualifiedAccess;CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module Submission =
    let private isCorrect returnType expected actual =
        let rec isOK (BasicValue (refType, refVal)) (BasicValue (_, actVal)) =
            let elemCmp (refType : BasicType, refVal : obj) (otherValue : obj) =
                //Convert.ChangeType(refVal, refType.clrType) = Convert.ChangeType(otherValue, refType.clrType)
                match refType with
                | Int -> (refVal :?> int) = (otherValue :?> int)
                | Double -> (refVal :?> float) = (otherValue :?> float)
                | Char -> (refVal :?> char) = (otherValue :?> char)
                | String -> (refVal :?> string) = (otherValue :?> string)
                | Bool -> (refVal :?> bool) = (otherValue :?> bool)
                | _ -> failwith "...should never reach here."
            match refType with
            | Int | Double | Char | String | Bool -> elemCmp (refType, refVal) actVal
            | Array elemType | GenericList elemType ->
                let refColl = Convert.ChangeType(refVal, refType.clrType) :?> System.Collections.IEnumerable
                let actColl = Convert.ChangeType(actVal, refType.clrType) :?> System.Collections.IEnumerable
                if actColl = null then false // refColl won't be null, at least not in CSc101 ...!  So when actColl is null, we know they can't match.
                else
                    let rec cmp (enum0 : System.Collections.IEnumerator) (enum1 : System.Collections.IEnumerator) =
                        let v0 = enum0.MoveNext ()
                        let v1 = enum1.MoveNext ()
                        if v0 <> v1 then false
                        elif v0 = false then true
                        elif (Convert.ChangeType(enum0.Current, elemType.clrType)) <> (Convert.ChangeType(enum1.Current, elemType.clrType)) then false
                        else cmp enum0 enum1
                    cmp (refColl.GetEnumerator()) (actColl.GetEnumerator())
                    //if Seq.length refColl <> Seq.length actColl then false
                    //else Seq.forall2 (fun a b -> isOK (BasicValue (elemType, a)) (BasicValue (elemType, b))) refColl actColl
        try
            isOK expected (BasicValue (returnType, actual))
        with
        | e -> raise e

    let private isDefaultImplementation (submission : FileInfo) (signature : Signature) (_default : Option<Instruction[]>) =
        _default |> Option.exists (fun _default ->
            Common.getMethodDefinition submission (fun m -> m.Name = signature.Name)
            |> Option.exists (fun m ->
                let isSameImplementation (a : seq<Instruction>) (b : seq<Instruction>) =
                    let isSame (x : Instruction, y : Instruction) =
                        if x.OpCode <> y.OpCode then false
                        else
                            match x.Operand, y.Operand with
                            | ((:? TypeReference as xDefn), (:? TypeReference as yDefn)) -> xDefn.FullName = yDefn.FullName
                            | ((:? FieldReference as xDefn), (:? FieldReference as yDefn)) -> xDefn.FullName = yDefn.FullName
                            | ((:? MethodReference as xDefn), (:? MethodReference as yDefn)) -> xDefn.FullName = yDefn.FullName
                            | _ -> true // well ... as long as the opcodes match ... ?
                    Seq.zip a b |> Seq.forall isSame
                let candidateBody = m.Body.Instructions.ToArray ()
                if candidateBody.Length <> _default.Length then false
                else isSameImplementation candidateBody _default
            )
        )

    let mark (submission : UnprocessedSubmission) (reference : Reference) : SubmissionWithResults =
        let markSingleQuestion (q : Question) (asm : System.Reflection.Assembly) : Result =
            let m =
                either {
                    let! m =
                        Common.getMethod q.Method.Name asm
                        |> Either.wrapError (function MethodNotFound _  -> ())
                    let! signature =
                        Common.parseSignature m |> Either.wrapError (function _ -> ())
                    if signature <> q.Method then return! Error ()
                    if isDefaultImplementation submission.Candidate.Executable q.Method q.DefaultBody then return! Error ()
                    return m
                }
            match m with
            | Error () -> QuestionNotFound q.Method
            | OK m ->
                let classType = m.DeclaringType
                let foldOverInputs state ({Arguments=args; Expected=expected} as testcase) =
                    match state with
                    | Timeout _ | QuestionNotFound _ | Failed _ -> state
                    | Pass _ ->
                        let argsArray = args |> List.map (fun v -> v.copy |> BasicValue.value) |> List.toArray
                        let stopwatch = System.Diagnostics.Stopwatch.StartNew()
                        let result =
                            Common.asSTA (Some 10000) (fun () ->
                                let o = Activator.CreateInstance(classType.Assembly.FullName, classType.FullName).Unwrap()
                                let retval = m.Invoke(o, argsArray)
                                retval
                            )
                        stopwatch.Stop ()
                        match result with
                        | Error TimeoutExceeded -> // this indicates a timeout.
                            Timeout { Case=testcase; Elapsed=stopwatch.Elapsed; Method=q.Method; Marks=q.Mark }
                        | Error (TimedExecutionFailed exn) ->
                            let reason = ExceptionRaised { Message=exn.Message; StackTrace=exn.StackTrace }
                            Failed { Case=testcase; Reason=reason; Method=q.Method; Marks=q.Mark }
                        | OK retval ->
                            if isCorrect q.Method.ReturnType expected retval then state
                            else
                                let reason = IncorrectValue (BasicValue (q.Method.ReturnType, retval))
                                Failed { Case=testcase; Reason=reason; Method=q.Method; Marks=q.Mark }
                q.Inputs |> Seq.fold foldOverInputs (Pass {Marks=q.Mark; Method=q.Method})
        let results =
            reference.Questions
            |> List.sortBy (fun q -> q.Mark, q.Method.Name)
            |> List.map (fun q ->
                Common.withExecutable submission.Candidate (markSingleQuestion q >> OK)
                |> Either.get
            )
        { CandidateID=submission.CandidateID; Candidate=submission.Candidate; Results=results }

[<RequireQualifiedAccess;CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module Build =
    let init (basePath : string) (_include : string list) (exclude : string list) (extractID : string) tools : Either<BuildData,BuildError> =
        either {
            if not (Directory.Exists basePath) then return! Error BasePathDoesNotExist
            let! _include = Common.asRegexes _include |> Either.wrapError IncludeRegexError
            let! exclude = Common.asRegexes exclude |> Either.wrapError ExcludeRegexError
            let! extractID = Common.asRegexes [extractID] |> Either.wrapError ExtractRegexError
            let extractID = List.head extractID // NOTE: extractID should contain a single Group.  I don't check for this, but I assume it later on!!
            return {BasePath=DirectoryInfo(basePath); Include=_include; Exclude=exclude; ExtractID=extractID; ToolsVersion=tools}
        }

    let internal buildProject extractId tools (projectFile : FileInfo) : BuildResult =
        printfn "Building: %s" projectFile.FullName
        let binDir = Path.Combine [|projectFile.DirectoryName ; "bin"|]
        if not <| Directory.Exists binDir then Directory.CreateDirectory binDir |> ignore
        // get the identity
        let ident = extractId projectFile.FullName
        // figure out if this has been built within the last 45 minutes.  If so - leave it alone.
        let recentEnough =
            let t = DateTime.Now.Subtract(TimeSpan.FromMinutes(480.)) // did I say 45 minutes?  I meant .... 8 hours
            Directory.EnumerateFiles(binDir, "*.exe", SearchOption.AllDirectories)
            |> Seq.exists (fun f -> FileInfo(f).CreationTime >= t)
        if recentEnough then
            let exe =
                Directory.EnumerateFiles(binDir, "*.exe", SearchOption.AllDirectories)
                |> Seq.head |> FileInfo |> Common.getExecutable
            BuildSuccess { CandidateID=ident; Candidate=exe }
        else
            // manually clean, for a start.
            let del x = if Directory.Exists x then Directory.Delete(x, true)
            del binDir
            del (Path.Combine [|projectFile.DirectoryName ; "obj"|])
            // now work it; based on https://stackoverflow.com/a/42816251
            let errorList = ref []
            let logger =
                let mutable p = ""
                let mutable v = Microsoft.Build.Framework.LoggerVerbosity.Minimal
                { new Microsoft.Build.Framework.ILogger with
                    member __.Parameters with get () = p and set v = p <- v
                    member __.Verbosity with get () = v and set x = v <- x
                    member __.Shutdown () = ()
                    member __.Initialize(eventSource : Microsoft.Build.Framework.IEventSource) =
                        eventSource.ErrorRaised
                        |> Event.add (fun x ->
                            let s = sprintf "[Line %d, %s] %s" x.LineNumber x.File x.Message
                            errorList := s :: !errorList
                        )
                }
            using (new Microsoft.Build.Evaluation.ProjectCollection(DefaultToolsVersion = string tools)) (fun csproj ->
                // if MSBuild starts doing something messed-up, uncomment the incredibly detailed logger below.
                let buildParams = BuildParameters(csproj, Loggers = [| logger; (*Microsoft.Build.Logging.ConsoleLogger(Microsoft.Build.Framework.LoggerVerbosity.Diagnostic)*) |], DefaultToolsVersion = string tools)
                let globals =
                    let d = System.Collections.Generic.Dictionary<_,_>()
                    d.["Configuration"] <- "Debug"
                    d.["VisualStudioVersion"] <- string tools
                    // I only figured out the necessary invocation below because of MSBuild diagnostic logging (see above) ... (and a bit of 'net background knowledge helped, too)
                    d.["CscToolPath"] <- Microsoft.Build.Utilities.ToolLocationHelper.GetPathToBuildTools(string tools)
                    d.["AssemblyName"] <- ident // this is important. If assembly names are the same, .Net can get very confused when creating types.
                    d
                //BuildManager.DefaultBuildManager.ResetCaches ()
                let request = BuildRequestData(projectFile.FullName, globals, string tools, [|"Clean";"Build"|], null)
                let result = BuildManager.DefaultBuildManager.Build(buildParams, request)
                if result.OverallResult = BuildResultCode.Success then
                    printfn "Succeeded."
                    match Directory.EnumerateFileSystemEntries(binDir, "*.exe", SearchOption.AllDirectories) |> Seq.toList with
                    | exe::_ -> BuildSuccess { CandidateID=ident; Candidate=Common.getExecutable (FileInfo(exe)) }
                    | [] ->
                        BuildFailure { CandidateID=ident; ProjectFile=projectFile; Reason="Project failed to build, though it claimed to succeed ... compile manually??"; ToolsVersion=tools }
                else
                    printfn "Failed.\n%s" (!errorList |> String.concat "\n   - ")
                    BuildFailure { CandidateID=ident; ProjectFile=projectFile; Reason = !errorList |> String.concat "\n"; ToolsVersion=tools }
            )

    let retry (failed : BuildFailure) : BuildResult =
        buildProject (fun _ -> failed.CandidateID) failed.ToolsVersion failed.ProjectFile

    let run (data : BuildData) : BuildResult list =
        Directory.EnumerateFiles(data.BasePath.FullName, "*.csproj", SearchOption.AllDirectories)
        |> Seq.filter (fun path -> data.Include |> List.exists (fun re -> re.IsMatch path))
        |> Seq.filter (fun path -> not (data.Exclude |> List.exists (fun re -> re.IsMatch path)))
        |> Seq.toList
        |> List.map (fun path ->
            buildProject (fun name -> data.ExtractID.Match(name).Groups.[1].Value (* ... this may break fairly easily *)) data.ToolsVersion (FileInfo(path))
        )        
            
[<RequireQualifiedAccess;CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module Reference =
    let init (refExecutable : string) (markmap : System.Collections.Generic.IDictionary<string,int>) : Either<Reference,ReferenceError> =
        either {
            if not (File.Exists refExecutable) then return! Error ReferenceExecutableDoesNotExist
            return! Common.getReference (FileInfo refExecutable) markmap
        }