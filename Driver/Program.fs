open UnitTestMarker
open UnitTestMarker.Data

let partition (results : BuildResult list) =
    let fine, notfine = results |> List.partition (function BuildSuccess _ -> true | _ -> false)
    List.map BuildResult.success fine, List.map BuildResult.failure notfine

let rec rebuild (ok : UnprocessedSubmission list) (failed : BuildFailure list) =
    match failed with
    | [] -> ok
    | something ->
        something |> Seq.iter (fun {ProjectFile=p} -> printfn "Failed: %s" p.FullName)
        printfn "Press <enter> when you'd like to retry these."
        System.Console.ReadLine () |> ignore
        let retried = something |> List.map Build.retry
        let fine, notfine = partition retried
        rebuild (fine @ ok) notfine

type SubmissionsError =
| ReferenceProblem of ReferenceError
| BuildProblem of BuildError

[<EntryPoint>]
let main argv = 
    let questions =
        [
            "Polarity", 5
            "InRange", 7
            "Sum", 8
            "FireSale", 10
            "IndexOfGEQ", 10
            "DivvyUp", 12
            "Splitter", 13
            "OnlyYou", 16
            "GotWords", 18
            "BigSmall", 18
            "RotL", 20
            "SpecialNumber", 30
            "Decode", 46
        ]
    let submissions =
        either {
            let! reference =
                Reference.init @"C:\Users\Me\Desktop\PartB\PracExamJune2017\bin\Debug\PracExamJune2017.exe" (Map.ofList questions)
                |> Either.wrapError ReferenceProblem   
            let! buildData =
                Build.init @"c:\temp\CSc101 Practical Exam, June 2017" [".*PartB.*.+\.csproj$"] [".*ORIGINAL.*"] ".*(Exam\d\d\d\d).*" Tools14
                |> Either.wrapError BuildProblem
            let fine, notfine = Build.run buildData |> partition
            let unprocessed = rebuild fine notfine
            //System.IO.File.WriteAllText("output.csv", sprintf ",%s\n" (reference.Questions |> List.map (fun q -> q.Method.Name) |> String.concat ","))
            //let sanitycheck = Submission.mark { CandidateID="SANITYCHECK"; Candidate=reference.Executable } reference
            let marked =
                unprocessed |> List.iteri (fun idx sub ->
                    let signatures = reference.Questions |> List.map (fun q -> q.Method)
                    let copied = MethodCopier.copy signatures sub
                    let sub = { sub with Candidate=copied }
                    let marked = Submission.mark sub reference
                    printfn "Marked %s" sub.CandidateID
                    if idx = 0 then
                        System.IO.File.WriteAllText("output.csv", marked.Results |> List.map (fun result ->
                            match result with
                            | Pass {Method={Name=name}}
                            | Failed {Method={Name=name}}
                            | QuestionNotFound {Name=name}
                            | Timeout {Method={Name=name}} -> name
                        ) |> String.concat "," |> sprintf ",%s\n")
                        if System.IO.File.Exists "detailed_output.log" then System.IO.File.Delete "detailed_output.log"
                    let csvLine =
                        sprintf "%s,%s\n" marked.CandidateID (marked.Results |> List.map (fun result ->
                            match result with
                            | Pass {Marks=m} -> string m
                            | Failed _ -> "0"
                            | Timeout _ -> "?"
                            | QuestionNotFound _ -> ""
                        ) |> String.concat ",")
                    let diagnosticLines =
                        let paramsFormat (x : TestCase) = (x.Arguments |> Seq.map (sprintf "`%O`") |> String.concat ", " |> sprintf "(%s)")
                        (sprintf "### %s" marked.CandidateID) :: (marked.Results |> List.choose (fun result ->
                            match result with
                            | Pass d -> Some <| sprintf "`%s` attempted and passes tests (+%d marks)" d.Method.Name d.Marks
                            | Failed d ->
                                match d.Reason with
                                | ExceptionRaised exn ->
                                    Some <| sprintf "`%s`, worth %d marks, attempted but throws exception: %s" d.Method.Name d.Marks exn.Message
                                | IncorrectValue actual ->
                                    Some <| sprintf "`%s`, worth %d marks, attempted but fails test.  With input %O, expected `%O` but got `%O`"
                                        d.Method.Name d.Marks (paramsFormat d.Case) d.Case.Expected actual
                            | QuestionNotFound signature ->
                                None //sprintf "`%s` not found" signature.Name
                            | Timeout d ->
                                Some <| sprintf "`%s`, worth %d marks, attempted but timed out (after %f seconds) on test input %s"
                                    d.Method.Name d.Marks d.Elapsed.TotalSeconds (paramsFormat d.Case)
                        ) |> List.map (sprintf "- %s"))
                    System.IO.File.AppendAllLines("detailed_output.log", diagnosticLines)
                    System.IO.File.AppendAllText("output.csv", csvLine)
                )
            return marked
        }

    match submissions with
    | Error x -> printfn "%A" x
    | _ -> ()
    0 // return an integer exit code
