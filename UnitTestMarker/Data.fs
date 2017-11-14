module UnitTestMarker.Data

open System
open System.IO
open System.Text.RegularExpressions
open Mono.Cecil.Cil

type Executable = {
    Executable : FileInfo
    Dependencies : FileInfo list
}        

type BasicType = String | Int | Bool | Char | Double | Array of BasicType | GenericList of BasicType
with
    member __.clrType =
        match __ with
        | String -> typeof<System.String>
        | Int -> typeof<System.Int32>
        | Bool -> typeof<System.Boolean>
        | Char -> typeof<System.Char>
        | Double -> typeof<System.Double>
        | Array elemType -> elemType.clrType.MakeArrayType()
        | GenericList elemType -> typedefof<System.Collections.Generic.List<_>>.MakeGenericType(elemType.clrType)

//module Magic =
//    let inline CloneArr< ^a when ^a :(member Clone : unit -> obj)> x = ( ^a : (member Clone : unit -> obj) x)

type BasicValue = BasicValue of BasicType * obj
with
    static member value = function BasicValue (_,v) -> v
    static member _type = function BasicValue (t,_) -> t
    override __.ToString () =
        let (BasicValue (t,v)) = __
        match t,v with
        | String, v -> sprintf "\"%s\"" (unbox v)
        | Int, v -> sprintf "%d" (unbox v)
        | Bool, v -> sprintf "%b" (unbox v)
        | Char, v -> sprintf "'%c'" (unbox v)
        | Double, v -> sprintf "%O" (unbox<float> v)
        | (Array elemType | GenericList elemType), v ->
            let v = Convert.ChangeType(v, t.clrType) :?> System.Collections.IEnumerable
            if v = null then "null" // refColl won't be null, at least not in CSc101 ...!  So when actColl is null, we know they can't match.
            else
                let rec go (enum : System.Collections.IEnumerator) accum =
                    let v = enum.MoveNext ()
                    if v = false then List.rev accum
                    else go enum (sprintf "%O" (BasicValue (elemType, enum.Current)) :: accum)
                go (v.GetEnumerator()) [] |> String.concat ", "
                |> sprintf "[%s]"

    member __.copy =
        let (BasicValue (t,v)) = __
        match t with
        | String | Int | Bool | Char | Double -> __
        | Array elemType ->
            if v = null then __
            else
                let mi = t.clrType.GetMethod("Clone")
                BasicValue (t, mi.Invoke(v, null))
        | GenericList elemType ->
            if v = null then __
            else
                // this next part ...... probably doesn't work.
                let x = Convert.ChangeType(v, t.clrType) :?> System.Collections.IEnumerable
                let enum = x.GetEnumerator()
                let list = Activator.CreateInstance(t.clrType) |> unbox<System.Collections.Generic.List<_>>
                while enum.MoveNext () do list.Add (unbox enum.Current)
                BasicValue (t, list)

type Signature = {
    ReturnType : BasicType
    Name : string
    Parameters : BasicType list
}

type TestCase = {
    Arguments : BasicValue list
    Expected : BasicValue
}

type Question = {
    Mark : int // a mark.
    Inputs : TestCase list
    Method : Signature
    DefaultBody : Option<Instruction[]>
}

type ExceptionData = {
    Message : string
    StackTrace : string
}

type FailureReason =
| IncorrectValue of BasicValue
| ExceptionRaised of ExceptionData

type TestCaseFailure = {
    Marks : int
    Case : TestCase
    Reason : FailureReason
    Method : Signature
}

type TestCaseTimeout = {
    Marks : int
    Method : Signature
    Case : TestCase
    Elapsed : TimeSpan
}

type TestCaseSuccess = {
    Marks : int
    Method : Signature
}

type Result =
| Pass of TestCaseSuccess
| Failed of TestCaseFailure
| Timeout of TestCaseTimeout
| QuestionNotFound of Signature

type Reference = {
    Executable : Executable
    Questions : Question list
}

type UnprocessedSubmission = {
    CandidateID : string
    Candidate : Executable
}

type SubmissionWithResults = {
    CandidateID : string
    Candidate : Executable
    Results : Result list
}

//type Builder = Path -> Executable option
//type Runner = Reference -> Executable -> Run list

type ToolsVersion = Tools12 | Tools14
with
    override __.ToString () = match __ with Tools12 -> "12.0" | Tools14 -> "14.0"

type BuildFailure = {
    CandidateID : string
    ToolsVersion : ToolsVersion
    ProjectFile : FileInfo
    Reason : string
}

type BuildResult =
| BuildSuccess of UnprocessedSubmission
| BuildFailure of BuildFailure
with
    static member success = function BuildSuccess x -> x | _ -> failwith "Item is not BuildSuccess"
    static member failure = function BuildFailure x -> x | _ -> failwith "Item is not BuildFailure"

type BuildData = {
    BasePath : DirectoryInfo
    Include : Regex list
    Exclude : Regex list
    ExtractID : Regex
    ToolsVersion : ToolsVersion
}

type BuildError =
| BasePathDoesNotExist
| IncludeRegexError of string
| ExcludeRegexError of string
| ExtractRegexError of string

type TimedExecutionError =
| TimeoutExceeded
| TimedExecutionFailed of exn

type TypeError = UnsupportedType of System.Type
with static member unwrap (UnsupportedType t) = t

type SignatureError =
| UnsupportedReturnType of System.Type
| UnsupportedParameterType of int * System.Type // parameter #n

type MethodError = MethodNotFound of string

type ReadInputsError =
| TestCasesNotFound of MethodError
| TestCaseReadingFailed of TimedExecutionError

type ReferenceError =
| ReferenceExecutableDoesNotExist
| ReferenceMethodNotFound of MethodError
| UnparseableReferenceSignature of SignatureError
| InputsError of ReadInputsError

type Either<'a,'b> =
| OK of 'a
| Error of 'b

[<RequireQualifiedAccess;CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module Either =
    let inline isOK x = match x with OK _ -> true | _ -> false
    let inline isError x = match x with Error _ -> true | _ -> false
    let get x = match x with OK v -> v | _ -> failwith "Either value is not `OK`"
    let error x = match x with Error s -> s | _ -> failwith "Either value is not `Error`"
    let bind (transform : 'a -> Either<'c,'b>) (state : Either<'a,'b>) : Either<'c,'b> =
        match state with
        | Error x -> Error x
        | OK y -> transform y
    let wrapError (transform : 'b -> 'c) (state : Either<'a,'b>) : Either<'a,'c> =
        match state with
        | Error x -> Error (transform x)
        | OK y -> OK y
    let map (transform : 'a -> Either<'b,'c>) (items : 'a seq) : Either<'b list, 'c> =
        items
        |> Seq.fold (fun state item ->
            match state with
            | Error _ -> state
            | OK accum -> match transform item with Error x -> Error x | OK v -> OK (v :: accum)
        ) (OK [])

type EitherBuilder () =
    member __.Bind(state : Either<'a,'b>, transform : 'a -> Either<'c,'b>) : Either<'c,'b> = Either.bind transform state

    member __.Return(value : 'a) : Either<'a,'b> = OK value

    member __.ReturnFrom(wrapped : Either<'a,'b>) = wrapped

    member __.Zero () : Either<'a,'b> = OK (Unchecked.defaultof<'a>)

    member __.Combine(x : Either<'a,'b>, y : Either<'a,'b>) : Either<'a,'b> =
        match x with
        | Error _ -> x
        | _ -> y

    member __.Delay(f : unit -> Either<'a,'b>) : Either<'a,'b> = f ()

    member __.Yield(x : 'a) : Either<'a,'b> = OK x

    member __.YieldFrom(x : Either<'a,'b>) = x

[<AutoOpen>]
module AutoLoad =
    let either = EitherBuilder ()
