package cats
package free

import scala.annotation.tailrec

import cats.data.Xor, Xor.{Left, Right}
import cats.arrow.NaturalTransformation

object Free {

  private sealed trait Fun[A, B] {
    def andThen[C](f: B => C): Fun[A, C] = this andThen Fun.Wrap(f)
    def andThen[C](f: Fun[B, C]): Fun[A, C] = Fun.AndThen(this, f)
    def apply(a: A): B = Fun.Eval(a, this).eval
  }

  private object Fun {
    final case class Wrap[A, B](f: A => B) extends Fun[A, B]
    final case class AndThen[A, B, C](f: Fun[A, B], g: Fun[B, C]) extends Fun[A, C]

    sealed trait Eval[B] {
      type A
      val a: A
      val fun: Fun[A, B]

      @tailrec def eval: B = fun match {
        case Wrap(f) => f(a)
        case AndThen(Wrap(f), g) => Eval(f(a), g).eval
        case AndThen(AndThen(f, g), h) => Eval(a, f andThen (g andThen h)).eval
      }
    }
    object Eval {
      def apply[A0, B](a0: A0, f: Fun[A0, B]): Eval[B] = new Eval[B] {
        type A = A0
        val a = a0
        val fun = f
      }
    }
  }

  /**
   * Return from the computation with the given value.
   */
  private final case class Pure[S[_], A](a: A) extends Free[S, A]

  /** Suspend the computation with the given suspension. */
  private final case class Suspend[S[_], A](a: S[A]) extends Free[S, A]

  /** Call a subroutine and continue with the given function. */
  private final case class Gosub[S[_], B, C](c: S[C] Xor C, f: Fun[C, Free[S, B]]) extends Free[S, B]

  /**
   * Suspend a value within a functor lifting it to a Free.
   */
  def liftF[F[_], A](value: F[A]): Free[F, A] = Suspend(value)

  /** Suspend the Free with the Applicative */
  def suspend[F[_], A](value: => Free[F, A])(implicit F: Applicative[F]): Free[F, A] =
    liftF(F.pure(())).flatMap(_ => value)

  /** Lift a pure value into Free */
  def pure[S[_], A](a: A): Free[S, A] = Pure(a)

  final class FreeInjectPartiallyApplied[F[_], G[_]] private[free] {
    def apply[A](fa: F[A])(implicit I : Inject[F, G]): Free[G, A] =
      Free.liftF(I.inj(fa))
  }

  def inject[F[_], G[_]]: FreeInjectPartiallyApplied[F, G] = new FreeInjectPartiallyApplied

  /**
   * `Free[S, ?]` has a monad for any type constructor `S[_]`.
   */
  implicit def freeMonad[S[_]]: Monad[Free[S, ?]] =
    new Monad[Free[S, ?]] {
      def pure[A](a: A): Free[S, A] = Free.pure(a)
      override def map[A, B](fa: Free[S, A])(f: A => B): Free[S, B] = fa.map(f)
      def flatMap[A, B](a: Free[S, A])(f: A => Free[S, B]): Free[S, B] = a.flatMap(f)
    }
}

import Free._

/**
 * A free operational monad for some functor `S`. Binding is done
 * using the heap instead of the stack, allowing tail-call
 * elimination.
 */
sealed abstract class Free[S[_], A] extends Product with Serializable {

  final def map[B](f: A => B): Free[S, B] =
    flatMap(a => Pure(f(a)))

  /**
   * Bind the given continuation to the result of this computation.
   * All left-associated binds are reassociated to the right.
   */
  final def flatMap[B](f: A => Free[S, B]): Free[S, B] = this match {
    case Pure(a) => Gosub(Xor.right(a), Fun.Wrap(f))
    case Suspend(sa) => Gosub(Xor.left(sa), Fun.Wrap(f))
    case Gosub(c, g) => Gosub(c, g.andThen(_.flatMap(f)))
  }

  /**
   * Catamorphism. Run the first given function if Pure, otherwise,
   * the second given function.
   */
  final def fold[B](r: A => B, s: S[Free[S, A]] => B)(implicit S: Functor[S]): B =
    resume.fold(s, r)

  /**
   * Evaluate a single layer of the free monad.
   */
  @tailrec
  final def resume(implicit S: Functor[S]): S[Free[S, A]] Xor A = this match {
    case Pure(a) => Right(a)
    case Suspend(t) => Left(S.map(t)(Pure(_)))
    case Gosub(Xor.Left(sc), f) => Left(S.map(sc)(f(_)))
    case Gosub(Xor.Right(c), f) => f(c).resume
  }

  /**
   * Run to completion, using a function that extracts the resumption
   * from its suspension functor.
   */
  final def go(f: S[Free[S, A]] => Free[S, A])(implicit S: Functor[S]): A = {
    @tailrec def loop(t: Free[S, A]): A =
      t.resume match {
        case Left(s) => loop(f(s))
        case Right(r) => r
      }
    loop(this)
  }

  final def run(implicit S: Comonad[S]): A = go(S.extract)

  /**
   * Run to completion, using a function that maps the resumption
   * from `S` to a monad `M`.
   */
  final def runM[M[_]](f: S[Free[S, A]] => M[Free[S, A]])(implicit S: Functor[S], M: Monad[M]): M[A] = {
    def runM2(t: Free[S, A]): M[A] = t.resume match {
      case Left(s) => Monad[M].flatMap(f(s))(runM2)
      case Right(r) => Monad[M].pure(r)
    }
    runM2(this)
  }

  /**
   * Catamorphism for `Free`.
   *
   * Run to completion, mapping the suspension with the given transformation at each step and
   * accumulating into the monad `M`.
   */
  @tailrec
  final def foldMap[M[_]](f: NaturalTransformation[S,M])(implicit M: Monad[M]): M[A] =
    this match {
      case Pure(a) => M.pure(a)
      case Suspend(sa) => f(sa)
      case Gosub(Xor.Left(sc), g) => M.flatMap(f(sc))(c => g(c).foldMap0(f))
      case Gosub(Xor.Right(c), g) => g(c).foldMap(f)
    }

  /** Alias for foldMap to be used inside foldMap in a non-tail position. */
  private final def foldMap0[M[_]](f: NaturalTransformation[S,M])(implicit M: Monad[M]): M[A] = foldMap(f)

  /**
   * Compile your Free into another language by changing the suspension functor
   * using the given natural transformation.
   * Be careful if your natural transformation is effectful, effects are applied by mapSuspension.
   */
  @tailrec
  final def mapSuspension[T[_]](f: NaturalTransformation[S,T]): Free[T, A] =
    this match {
      case Pure(a) => Pure(a)
      case Suspend(sa) => Suspend(f(sa))
      case Gosub(Xor.Left(sc), g) => Gosub(Xor.left(f(sc)), g.andThen(_.mapSuspension0(f)))
      case Gosub(Xor.Right(c), g) => g(c).mapSuspension(f)
    }

  /** Alias for mapSuspension to be used inside mapSuspension in a non-tail position. */
  final def mapSuspension0[T[_]](f: NaturalTransformation[S,T]): Free[T, A] =
    mapSuspension(f)

  final def compile[T[_]](f: NaturalTransformation[S,T]): Free[T, A] = mapSuspension(f)

}
