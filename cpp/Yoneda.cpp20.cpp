// This is Yoneda's lemma in C++20?
// which is derived from one in Scala by https://www.slideshare.net/100005930379759/scala-scala

#include <functional>
#include <algorithm>
#include <vector>
#include <iostream>
#include <string>
#include <concepts>

// (generic) function type is verbose in C++
template<typename X, typename Y>
using Hom = std::function<Y(X)>;

namespace { // arbitrary types
    class XX;
    class YY;
}

// mapOb<X> for object mapping and map() for morphism mapping 
template<typename F>
concept EndoFunctor = requires(XX xx, YY yy) {
    typename F::template mapOb<XX>;
    { std::declval<const F>().map(std::declval<Hom<XX, YY>>()) }
    -> std::same_as<Hom<typename F::template mapOb<XX>, typename F::template mapOb<YY>>>;
};

// Natural transformation: F and G are functors
template<typename T, typename F, typename G>
concept Nat = EndoFunctor<F> && EndoFunctor<G> &&
    requires(XX xx)
{
    typename T::FunctorF;
    requires std::same_as<typename T::FunctorF, F>;
    typename T::FunctorT;
    requires std::same_as<typename T::FunctorT, G>;
    typename T::template mapObF<XX>;
    requires std::same_as<
        typename T::template mapObF<XX>,
        typename F::template mapOb<XX>>;
    typename T::template mapObT<XX>;
    requires std::same_as<
        typename T::template mapObT<XX>,
        typename G::template mapOb<XX>>;
    { std::declval<const T>()(std::declval<typename T::template mapObF<XX>>()) }
    -> std::same_as<typename T::template mapObT<XX>>;
};
// used to define type aliases
template<EndoFunctor F, EndoFunctor G>
struct NatHelper
{
    using FunctorF = F;
    using FunctorT = G;
    template<typename X>
    using mapObF = typename FunctorF::template mapOb<X>;
    template<typename X>
    using mapObT = typename FunctorT::template mapOb<X>;
};

// Seq functor
template<typename T>
using Seq = std::vector<T>;
struct SeqFunctor
{
    template<typename X>
    using mapOb = Seq<X>;
    template<typename X, typename Y>
    Hom<mapOb<X>,mapOb<Y>> map(Hom<X,Y> f) const {
        return [f](mapOb<X> x){
            // C++20 range is not so helpful here because container I/F is still iterator base
            mapOb<Y> y(x.size());
            std::transform(x.begin(), x.end(), y.begin(), f);
            return y;
        };
    }
};

// Const functor: always mapping to the specific object and the specific morphism
template<typename T>
using Const = int;
#if !defined(__clang__)
// I'm not sure the reason.
// Without this, GCC produces errors like "invalid use of incomplete type ‘Hom<int, int>'"
template class std::function<int(int)>;
#endif

struct ConstFunctor
{
    template<typename X>
    using mapOb = Const<X>;
    template<typename X, typename Y>
    Hom<mapOb<X>,mapOb<Y>> map(Hom<X,Y> f) const {
        return [](mapOb<X> x){ return mapOb<Y>(x); };
    }
};

// a natural transformation from Seq functor to Const functor
struct length_ : NatHelper<SeqFunctor, ConstFunctor>
{
    template<typename X>
    Const<X> operator()(Seq<X> x) const { return x.size(); }
} length;
// a morphism mapped by functors
Hom<int, std::string> f = [](int i){ return std::to_string(i); };

// Yoneda's lemma
template<typename X>
struct HomFunctor
{
    using dom = X;
    template<typename A>
    using mapOb = Hom<X,A>;
    template<typename A, typename B>
    Hom<mapOb<A>,mapOb<B>> map(Hom<A,B> f) const
    {
        return [f](mapOb<A> xa){ return [f,xa](X x){ return f(xa(x)); }; };
        //                                                  ~~~~~~~~ b in B
        //                              ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ mapOb<B> = Hom<X,B>
    }
};

template<typename X, EndoFunctor F>
struct LiftY : NatHelper<HomFunctor<X>, F>
{
    LiftY(typename F::template mapOb<X> x) : x(x) {}
    template<typename A>
    typename F::template mapOb<A> operator()(Hom<X,A> f) const {
        return F().map(f)(x);
    }
    typename F::template mapOb<X> x;
};

template<typename X, EndoFunctor F>
LiftY<X, F>
liftY(typename F::template mapOb<X> x)
{
    return LiftY<X, F>(x);
}
template<typename NatHomX2F>
  requires Nat<NatHomX2F, typename NatHomX2F::FunctorF, typename NatHomX2F::FunctorT>
  && std::same_as<
    typename NatHomX2F::FunctorF::template mapOb<XX>,
    typename HomFunctor<typename NatHomX2F::FunctorF::dom>::template mapOb<XX>>
typename NatHomX2F::FunctorT::template mapOb<typename NatHomX2F::FunctorF::dom> lowerY(NatHomX2F f)
{
    using X = typename NatHomX2F::FunctorF::dom;
    Hom<X, X> idX = [](X x){ return x; };
    return f(idX);
}

int main(void)
{
    // Verify commutativity
    std::cout << length(SeqFunctor().map(f)(Seq<int>{0, 1, 2})) << std::endl;
    std::cout << ConstFunctor().map(f)(length(Seq<int>{0, 1, 2})) << std::endl;

    // Yoneda's lemma
    for(auto &v: lowerY(liftY<int, SeqFunctor>(Seq<int>{0,1,2}))) {
        std::cout << v << ' ';
    }
    std::cout << std::endl;

    return 0;
}