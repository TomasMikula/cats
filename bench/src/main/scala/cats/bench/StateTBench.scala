package cats.bench

import cats.{Eval, Id, Monad}
import cats.data.StateT
import org.openjdk.jmh.annotations.{Benchmark, Scope, State}

@State(Scope.Benchmark)
class StateTBench {

  def iteratedFlatMap[F[_]](n: Int)(implicit F: Monad[F]): StateT[F, Int, Int] =
    (1 to n).foldLeft(StateT.pure[F, Int, Int](n))((st, _) => st.flatMap(i => StateT(_ => F.pure((i-1, i-1)))))

  def recursiveFlatMap[F[_]](implicit F: Monad[F]): StateT[F, Int, Int] =
    StateT[F, Int, Int](n => F.pure((n-1, n-1))).flatMap(i =>
        if(i > 0) recursiveFlatMap
        else StateT.pure[F, Int, Int](0)
    )

  @Benchmark
  def strictIteratedFlatMap100: Int =
    iteratedFlatMap[Id](100).runA(0)

  @Benchmark
  def strictIteratedFlatMap100k: Int =
    iteratedFlatMap[Id](100000).runA(0)

  @Benchmark
  def strictRecursiveFlatMap100: Int =
    recursiveFlatMap[Id].runA(100)

  @Benchmark
  def strictRecursiveFlatMap100k: Int =
    recursiveFlatMap[Id].runA(100000)

  @Benchmark
  def trampolinedIteratedFlatMap100: Int =
    iteratedFlatMap[Eval](100).runA(0).value

  @Benchmark
  def trampolinedIteratedFlatMap100k: Int =
    iteratedFlatMap[Eval](100000).runA(0).value

  @Benchmark
  def trampolinedRecursiveFlatMap100: Int =
    recursiveFlatMap[Eval].runA(100).value

  @Benchmark
  def trampolinedRecursiveFlatMap100k: Int =
    recursiveFlatMap[Eval].runA(100000).value

}
