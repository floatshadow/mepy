signature TOP =
sig

    val test : unit -> OS.Process.status
    val main : string * string list -> OS.Process.status

end

structure Top :> TOP =
struct

fun test () =
    let
        val () = SaturateTest.test ()
        val () = LinearTest.test ()
        val () = OrderedTest.test ()
        val () = TextIO.print ("% regression testing succeeded\n")
    in
        OS.Process.success
    end
    handle _ => let val () = TextIO.print ("% regession testing failed\n")
                in
                    OS.Process.failure
                end

fun main (name, args) = test ()


end (* structure Test *)
