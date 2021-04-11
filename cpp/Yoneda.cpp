// This is Yoneda's lemma in C++11?
// which is derived from one in Scala by https://www.slideshare.net/100005930379759/scala-scala

#include <functional>
#include <algorithm>
#include <vector>
#include <iostream>
#include <string>

// (generic) function type is verbose in C++
template<typename X, typename Y>
using Hom = std::function<Y(X)>;

// mapOb<X> for object mapping and map() for morphism mapping 
#if 0 // not used actually, may become concept in C++20
template<template <typename> class F>
struct EndoFunctor
{
    template<typename X>
    using mapOb = F<X>;
    template<typename X, typename Y>
    Hom<mapOb<X>,mapOb<Y>> map(Hom<X,Y> f) const;
};
#endif

// Natural transformation: F and G are functors
// may become concept in C++20
// used to define type aliases
template<typename F, typename G>
struct Nat_
{
    using FunctorF = F;
    using FunctorT = G;
    template<typename X>
    using mapObF = typename FunctorF::template mapOb<X>;
    template<typename X>
    using mapObT = typename FunctorT::template mapOb<X>;
//  template<typename X>
//  mapObT<X> operator()(mapObF<X>) const;
};

// Seq functor
template<typename T>
using Seq = std::vector<T>;
struct SeqFunctor // : EndoFunctor<Seq>
{
    template<typename X>
    using mapOb = Seq<X>;
    template<typename X, typename Y>
    Hom<mapOb<X>,mapOb<Y>> map(Hom<X,Y> f) const {
        return [f](mapOb<X> x){
            mapOb<Y> y(x.size());
            std::transform(x.begin(), x.end(), y.begin(), f);
            return y;
        };
    }
};

// Const functor: always mapping to the specific object and the specific morphism
#if 1
template<typename T>
struct Const
{
    Const(int n):n(n) {}
    operator int() const { return n; }
    int n;
};
#else
// GCC rejects by invalid use of incomplete type ‘class std::function<Const<Y>(Const<X>)>’
// while CLANG accepts
template<typename T>
using Const = int;
#endif

struct ConstFunctor // : EndoFunctor<Const>
{
    template<typename X>
    using mapOb = Const<X>;
    template<typename X, typename Y>
    Hom<mapOb<X>,mapOb<Y>> map(Hom<X,Y> f) const {
        return [](mapOb<X> x){ return mapOb<Y>(x); };
    }
};

// a natural transformation from Seq functor to Const functor
struct length_ : Nat_<SeqFunctor, ConstFunctor>
{
    template<typename X>
    Const<X> operator()(Seq<X> x) const { return x.size(); }
} length;
// a morphism mapped by functors
Hom<int, std::string> f = [](int i){ return std::to_string(i); };

// Yoneda's lemma
//template<typename X>
//struct HomBind
//{
//    template<typename Y>
//    using Hom1 = Hom<X, Y>;
//};
template<typename X>
struct HomFunctor // : EndoFunctor<HomBind<X>::template Hom1>
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

template<typename X, typename F>
struct LiftY : Nat_<HomFunctor<X>, F>
{
    LiftY(typename F::template mapOb<X> x) : x(x) {}
    template<typename A>
    typename F::template mapOb<A> operator()(Hom<X,A> f) const {
        return F().map(f)(x);
    }
    typename F::template mapOb<X> x;
};

template<typename X, typename F>
LiftY<X, F>
liftY(typename F::template mapOb<X> x)
{
    return LiftY<X, F>(x);
}
// NatHomX2F has I/F like template<typename X, typename F> Nat_<HomFunctor<X>, F>
// may be bound by concept in C++20
template<typename NatHomX2F>
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