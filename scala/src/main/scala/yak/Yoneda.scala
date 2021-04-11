// This is Yoneda's lemma in Scala,
// which is an exceprt from https://www.slideshare.net/100005930379759/scala-scala
// with slight modification

object Main extends App {
  // F[_] for object mapping and map() for morphism mapping 
  trait EndoFunctor[F[_]] {
    def map[X, Y](f: X => Y): F[X] => F[Y]
  }
  // Pick a functor implementation by specifying Kind
  object EndoFunctor {
    def apply[F[_]](implicit instance: EndoFunctor[F]) : EndoFunctor[F] = instance
  }
  // Natural transformation: F and G are functors
  trait ~>[F[_], G[_]] {
    def apply[X](x: F[X]):G[X]
  }
  // Seq functor
  implicit val seqFunctor = new EndoFunctor[Seq] {
    def map[X, Y](f: X => Y): Seq[X] => Seq[Y] = _.map(f)
  }
  // Const functor: always mapping to the specific object and the specific morphism
  type Const[X] = Int
  implicit val constFunctor = new EndoFunctor[Const] {
    def map[X,Y](f: X => Y): Const[X] => Const[Y] = x => x // always mapping to an identity morphism
  }
  // a natural transformation from Seq functor to Const functor
  val length = new (Seq ~> Const) {
    def apply[X](x: Seq[X]): Const[X] = x.length
  }
  // a morphism mapped by functors
  val f: Int => String = x => s"$x"
  // Verify commutativity
  println( length(EndoFunctor[Seq].map(f)(Seq(0, 1, 2))) )
  println( EndoFunctor[Const].map(f)(length(Seq(0, 1, 2))) )

  // Yoneda's lemma
  type Hom[X, Y] = X => Y
  // Without kind-projector, Hom[X, *] should be written as like ({type HomXTo[Y] = Hom[X, Y]})#HomXTo
  def liftY[F[_], X](x: F[X])(implicit F: EndoFunctor[F]): Hom[X, *] ~> F =
    new (Hom[X, *] ~> F) {
      def apply[A](f: Hom[X, A]): F[A] = EndoFunctor[F].map(f)(x)
    }
  def lowerY[F[_], X](f: Hom[X, *] ~> F): F[X] = f(x => x)


  println( lowerY(liftY(Seq(0, 1, 2))) )
}