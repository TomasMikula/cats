package cats
package free

import scala.annotation.tailrec

import cats.data.Xor, Xor.{Left, Right}
import cats.arrow.NaturalTransformation

object Free {

  /** Natural transformation with stack-safe composition. */
  private sealed trait Nat[S[_], T[_]] {
    def andThen[U[_]](g: NaturalTransformation[T, U]): Nat[S, U] = Nat.AndThen(this, Nat.Wrap(g))
    def andThen[U[_]](g: Nat[T, U]): Nat[S, U] = Nat.AndThen(this,g)
    final def apply[A](s: S[A]): T[A] = Nat.Applicator(s, this).eval
  }
  private object Nat {
    final case class Wrap[S[_], T[_]](f: NaturalTransformation[S, T]) extends Nat[S, T]
    final case class AndThen[S[_], T0[_], U[_]](f0: Nat[S, T0], g0: Nat[T0, U]) extends Nat[S, U] {
      type T[X] = T0[X]
      def f: Nat[S, T] = f0
      def g: Nat[T, U] = g0
    }

    sealed abstract class Applicator[T[_], A] {
      type S[_]
      val s: S[A]
      val f: Nat[S, T]

      @tailrec
      final def eval: T[A] = f match {
        case Wrap(f0) => f0(s)
        case c @ AndThen(_, _) => c.f match {
          case Wrap(f0) => Applicator(f0(s), c.g).eval
          case d @ AndThen(_, _) => Applicator(s, d.f andThen (d.g andThen c.g)).eval
        }
      }
    }
    object Applicator {
      def apply[S0[_], T[_], A](s0: S0[A], f0: Nat[S0, T]): Applicator[T, A] = new Applicator[T, A] {
        type S[X] = S0[X]
        val s = s0
        val f = f0
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
  private final case class Gosub[S[_], B, C](c: Free[S, C], f: C => Free[S, B]) extends Free[S, B]

  private final case class MapSusp[S0[_], T[_], A0](a0: Free[S0, A0], f0: Nat[S0, T]) extends Free[T, A0] {
    type S[X] = S0[X]
    type A = A0
    def a: Free[S, A] = a0
    def f: Nat[S, T] = f0
  }

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
    flatMap(a => pure(f(a)))

  /**
   * Bind the given continuation to the result of this computation.
   * All left-associated binds are reassociated to the right.
   */
  final def flatMap[B](f: A => Free[S, B]): Free[S, B] =
    Gosub(this, f)

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
    case Gosub(c, f) =>
      c match {
        case Pure(a) => f(a).resume
        case Suspend(t) => Left(S.map(t)(f))
        case Gosub(d, g) => d.flatMap(dd => g(dd).flatMap(f)).resume
        case ms @ MapSusp(_, _) => ms.a match {
          case Pure(a) => f(a).resume
          case Suspend(ta) => Left(S.map(ms.f(ta))(f))
          case Gosub(d, g) => d.mapSusp(ms.f).flatMap(g(_).mapSusp(ms.f)).flatMap(f).resume
          case ms1 @ MapSusp(_, _) => ms1.a.mapSusp(ms1.f andThen ms.f).flatMap(f).resume
        }
      }
    case ms @ MapSusp(_, _) => ms.a match {
      case Pure(a) => Right(a)
      case Suspend(ta) => Left(S.map(ms.f(ta))((a: A) => pure(a)))
      case Gosub(c, f) => (c.mapSusp(ms.f).flatMap(f(_).mapSusp(ms.f)): Free[S, A]).resume
      case ms1 @ MapSusp(_, _) => (ms1.a.mapSusp(ms1.f andThen ms.f): Free[S, A]).resume
    }
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
      case Gosub(fx, g) => fx match {
        case Pure(x) => g(x).foldMap(f)
        case Suspend(sx) => M.flatMap(f(sx))(g(_).foldMap0(f))
        case Gosub(fy, h) => fy.flatMap(h(_).flatMap(g)).foldMap(f)
        case ms @ MapSusp(_, _) => ms.a match {
          case Pure(x) => g(x).foldMap(f)
          case Suspend(tx) => M.flatMap(f(ms.f(tx)))((x: ms.A) => g(x).foldMap0(f))
          case Gosub(fty, h) => fty.mapSusp(ms.f).flatMap(y => h(y).mapSusp(ms.f).flatMap(g)).foldMap(f)
          case MapSusp(fux, ut) => fux.mapSusp(ut andThen ms.f).flatMap(g).foldMap(f)
        }
      }
      case ms @ MapSusp(_, _) => ms.a match {
        case Pure(a) => M.pure(a)
        case Suspend(ta) => f(ms.f(ta))
        case Gosub(ftx, g) => (ftx.mapSusp(ms.f).flatMap(g(_).mapSusp(ms.f)): Free[S, A]).foldMap(f)
        case MapSusp(fua, ut) => (fua.mapSusp(ut andThen ms.f): Free[S, A]).foldMap(f)
      }
    }

  private final def foldMap0[M[_]](f: NaturalTransformation[S,M])(implicit M: Monad[M]): M[A] =
    foldMap(f)

  /**
   * Compile your Free into another language by changing the suspension functor
   * using the given natural transformation.
   * Be careful if your natural transformation is effectful, effects are applied by mapSuspension.
   */
  final def mapSuspension[T[_]](f: NaturalTransformation[S,T]): Free[T, A] =
    mapSusp(Nat.Wrap(f))

  private final def mapSusp[T[_]](f: Nat[S, T]): Free[T, A] =
    MapSusp(this, f)

  final def compile[T[_]](f: NaturalTransformation[S,T]): Free[T, A] = mapSuspension(f)

}
