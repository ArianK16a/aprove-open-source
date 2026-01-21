package aprove.verification.complexity.LowerBounds.Types;

import java.util.*;
import java.util.concurrent.atomic.*;

import aprove.verification.complexity.LowerBounds.BasicStructures.Rule;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.domains.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * Inference of Simple Types.
 */
public class TypeInference {

    private static class FunctionSymbolArgumentType extends FunctionSymbolTypePosition {

        private int argument;

        public FunctionSymbolArgumentType(FunctionSymbol f, int argument) {
            super(f);
            this.argument = argument;
            assert argument >= 0 && argument < f.getArity();
        }

        @Override
        public boolean equals(Object obj) {
            if (this == obj) {
                return true;
            }
            if (!super.equals(obj)) {
                return false;
            }
            if (this.getClass() != obj.getClass()) {
                return false;
            }
            FunctionSymbolArgumentType other = (FunctionSymbolArgumentType) obj;
            if (this.argument != other.argument) {
                return false;
            }
            return true;
        }

        @Override
        public int hashCode() {
            int prime = 31;
            int result = super.hashCode();
            result = prime * result + this.argument;
            return result;
        }
    }

    private static class FunctionSymbolReturnType extends FunctionSymbolTypePosition {
        public FunctionSymbolReturnType(FunctionSymbol f) {
            super(f);
        }
    }

    private static abstract class FunctionSymbolTypePosition extends TypePosition {
        private FunctionSymbol f;

        public FunctionSymbolTypePosition(FunctionSymbol f) {
            this.f = f;
        }

        @Override
        public boolean equals(Object obj) {
            if (this == obj) {
                return true;
            }
            if (obj == null) {
                return false;
            }
            if (this.getClass() != obj.getClass()) {
                return false;
            }
            FunctionSymbolTypePosition other = (FunctionSymbolTypePosition) obj;
            if (this.f == null) {
                if (other.f != null) {
                    return false;
                }
            } else if (!this.f.equals(other.f)) {
                return false;
            }
            return true;
        }

        public FunctionSymbol getFunctionSymbol() {
            return this.f;
        }

        @Override
        public int hashCode() {
            int prime = 31;
            int result = 1;
            result = prime * result + ((this.f == null) ? 0 : this.f.hashCode());
            return result;
        }
    }

    private static abstract class TypePosition implements Immutable {
    }

    private static class VariableTypePosition extends TypePosition {
        private TRSVariable v;

        public VariableTypePosition(TRSVariable v) {
            this.v = v;
        }

        @Override
        public boolean equals(Object obj) {
            if (this == obj) {
                return true;
            }
            if (obj == null) {
                return false;
            }
            if (this.getClass() != obj.getClass()) {
                return false;
            }
            VariableTypePosition other = (VariableTypePosition) obj;
            if (this.v == null) {
                if (other.v != null) {
                    return false;
                }
            } else if (!this.v.equals(other.v)) {
                return false;
            }
            return true;
        }

        @Override
        public int hashCode() {
            int prime = 31;
            int result = 1;
            result = prime * result + ((this.v == null) ? 0 : this.v.hashCode());
            return result;
        }
    }

    public static TrsTypes infer(
        Collection<Rule> rules,
        Collection<FunctionSymbol> signature,
        Collection<FunctionSymbol> definedSymbols)
    {
        UnionFind<TypePosition> u = new UnionFind<>();

        for (Rule r : rules) {
            TypePosition leftType = TypeInference.inferType(r.getLeft(), u);
            TypePosition rightType = TypeInference.inferType(r.getRight(), u);
            u.union(leftType, rightType);
            for (TRSVariable v : r.getVariables()) {
                u.ignore(new VariableTypePosition(v));
            }
        }

        FreshNameGenerator fng = new FreshNameGenerator(FreshNameGenerator.TYPE_VARS);

        ImmutableSet<ImmutableSet<TypePosition>> partitions = u.getPartitions();

        Map<TypePosition, Type> types = new LinkedHashMap<>();
        for (ImmutableSet<TypePosition> partition : partitions) {
            Boolean isReturnTypeInteger = false;
            StringBuilder constrName = new StringBuilder();
            StringBuilder defName = new StringBuilder();
            for (TypePosition pos : partition) {
                if (pos instanceof FunctionSymbolArgumentType) {
                    FunctionSymbolArgumentType argType = (FunctionSymbolArgumentType) pos;
                    if (IDPPredefinedMap.DEFAULT_MAP.isArithmeticFunction(argType.getFunctionSymbol())) {
                        isReturnTypeInteger = true;
                    }
                }
                if (!(pos instanceof FunctionSymbolReturnType)) {
                    continue;
                }
                FunctionSymbolTypePosition fpos = (FunctionSymbolTypePosition)pos;
                FunctionSymbol f = fpos.getFunctionSymbol();
                if (definedSymbols.contains(f)) {
				   defName.append(f.getName()).append(":");
                } else {
                    constrName.append(f.getName()).append(":");
                }
                if (IDPPredefinedMap.DEFAULT_MAP.isInt(f, DomainFactory.INTEGERS) || IDPPredefinedMap.DEFAULT_MAP.isArithmeticFunction(f)) {
                    isReturnTypeInteger = true;
                }
            }
            String name = constrName.toString().isEmpty() ? defName.toString() : constrName.toString();
            if (!name.isEmpty()) {
                name = name.substring(0, name.length() - 1);
            } else {
                name = "a";
            }
            String typeName = fng.getFreshName(name, false);
            for (TypePosition pos : partition) {
                types.put(pos, isReturnTypeInteger ? Type.Nats : new Type(typeName));
            }
        }

        TrsTypes m = new TrsTypes();
        for (FunctionSymbol f : signature) {
            ArrayList<Type> argumentTypes = new ArrayList<>();
            int l = f.getArity();
            for (int i = 0; i < l; ++i) {
                argumentTypes.add(i, types.get(new FunctionSymbolArgumentType(f, i)));
            }
            FunctionSymbolSimpleType type =
                new FunctionSymbolSimpleType(
                    types.get(new FunctionSymbolReturnType(f)),
                    ImmutableCreator.create(argumentTypes));
            m.declare(f, type);
        }

        return m;
    }

    private static TypePosition inferType(TRSTerm t, UnionFind<TypePosition> u) {
        if (t.isVariable()) {
            return new VariableTypePosition((TRSVariable) t);
        }
        TRSFunctionApplication fa = (TRSFunctionApplication) t;
        FunctionSymbol f = fa.getRootSymbol();
        int l = f.getArity();
        for (int i = 0; i < l; ++i) {
            TRSTerm ti = fa.getArgument(i);
            u.union(TypeInference.inferType(ti, u), new FunctionSymbolArgumentType(f, i));
        }
        return new FunctionSymbolReturnType(f);
    }
    
    // ---------------------- Inference with name-free environment with real constructors ----------------------

    /** Opaque id for a union-find partition (= inferred sort). */
    public static final class ClassId {
        private final int id;
        public ClassId(int id) { this.id = id; }
        public int id() { return id; }
        @Override public int hashCode() { return Integer.hashCode(id); }
        @Override public boolean equals(Object o) { return (o instanceof ClassId c) && c.id == id; }
        @Override public String toString() { return "k" + id; }
    }

    /** Constructors that inhabit a sort (i.e., have this class as their result). */
    public static final class SortInfo {
        private final ClassId id;
        private final Set<FunctionSymbol> constructors; // result-constructors for this class
        public SortInfo(ClassId id, Set<FunctionSymbol> ctors) {
            this.id = id; this.constructors = Collections.unmodifiableSet(new LinkedHashSet<>(ctors));
        }
        public ClassId id() { return id; }
        public Set<FunctionSymbol> constructors() { return constructors; }
        @Override public String toString() { return "Sort(" + id + " ctors=" + constructors + ")"; }
    }

    /** Constructor signature in terms of class ids. */
    public static final class CtorSig {
        private final FunctionSymbol ctor;
        private final List<ClassId> argClasses;
        private final ClassId resultClass;
        public CtorSig(FunctionSymbol ctor, List<ClassId> args, ClassId res) {
            this.ctor = ctor;
            this.argClasses = List.copyOf(args);
            this.resultClass = res;
        }
        public FunctionSymbol ctor() { return ctor; }
        public List<ClassId> argClasses() { return argClasses; }
        public ClassId resultClass() { return resultClass; }
        @Override public String toString() { return "CtorSig(" + ctor + " : " + argClasses + " -> " + resultClass + ")"; }
    }

    /** Defined symbol signature in terms of class ids. */
    public static final class DefSig {
        private final FunctionSymbol def;
        private final List<ClassId> argClasses;
        private final ClassId resultClass;
        public DefSig(FunctionSymbol def, List<ClassId> args, ClassId res) {
            this.def = def; this.argClasses = List.copyOf(args); this.resultClass = res;
        }
        public FunctionSymbol def() { return def; }
        public List<ClassId> argClasses() { return argClasses; }
        public ClassId resultClass() { return resultClass; }
        @Override public String toString() { return "DefSig(" + def + " : " + argClasses + " -> " + resultClass + ")"; }
    }

    /** Name-free environment: sorts (UF classes) with their constructors, plus ctor/def signatures. */
    public static final class TypeEnv {
        private final Map<ClassId, SortInfo> sorts;
        private final Map<FunctionSymbol, CtorSig> ctors;
        private final Map<FunctionSymbol, DefSig> defs;
        public TypeEnv(Map<ClassId, SortInfo> sorts,
                       Map<FunctionSymbol, CtorSig> ctors,
                       Map<FunctionSymbol, DefSig> defs) {
            this.sorts = Collections.unmodifiableMap(new LinkedHashMap<>(sorts));
            this.ctors = Collections.unmodifiableMap(new LinkedHashMap<>(ctors));
            this.defs  = Collections.unmodifiableMap(new LinkedHashMap<>(defs));
        }
        public Map<ClassId, SortInfo> sorts() { return sorts; }
        public Map<FunctionSymbol, CtorSig> ctors() { return ctors; }
        public Map<FunctionSymbol, DefSig> defs() { return defs; }
        @Override public String toString() {
            return "TypeEnv{\n  sorts=" + sorts.values() + ",\n  ctors=" + ctors.values() + ",\n  defs=" + defs.values() + "\n}";
        }
    }

    /** Build a TypeEnv: real constructor sets per inferred sort (UF class), and class-based signatures. */
    public static TypeEnv inferEnv(
        ImmutableSet<aprove.verification.dpframework.BasicStructures.Rule> rules,
        ImmutableSet<FunctionSymbol> signature,
        ImmutableSet<FunctionSymbol> definedSymbols)
    {
        // 1) Constraint generation + unification
        UnionFind<TypePosition> u = new UnionFind<>();
        for (aprove.verification.dpframework.BasicStructures.Rule r : rules) {
            TypePosition leftType  = inferType(r.getLeft(),  u);
            TypePosition rightType = inferType(r.getRight(), u);
            u.union(leftType, rightType);
            for (TRSVariable v : r.getVariables()) u.ignore(new VariableTypePosition(v));
        }

        // 2) Partitions → stable ClassIds; map every TypePosition to its ClassId
        ImmutableSet<ImmutableSet<TypePosition>> partitions = u.getPartitions();
        Map<TypePosition, ClassId> classOf = new HashMap<>();
        List<ImmutableSet<TypePosition>> partsOrdered = new ArrayList<>(partitions);
        // Deterministic order: sort partitions by a stable key (size, then min hash)
        partsOrdered.sort(Comparator
            .<ImmutableSet<TypePosition>>comparingInt(Set::size)
            .thenComparingInt(s -> s.stream().mapToInt(Object::hashCode).min().orElse(0))
        );
        AtomicInteger nextId = new AtomicInteger(0);
        for (ImmutableSet<TypePosition> part : partsOrdered) {
            ClassId id = new ClassId(nextId.getAndIncrement());
            for (TypePosition pos : part) classOf.put(pos, id);
        }

        // 3) Scan signature; classify symbols as ctor or def; build sigs and collect ctors by result class
        Map<ClassId, Set<FunctionSymbol>> ctorsByResult = new LinkedHashMap<>();
        Map<FunctionSymbol, CtorSig> ctorSigs = new LinkedHashMap<>();
        Map<FunctionSymbol, DefSig>  defSigs  = new LinkedHashMap<>();

        for (FunctionSymbol f : signature) {
            ClassId res = classOf.get(new FunctionSymbolReturnType(f));
            if (res == null) {
                // Unconstrained result: create a fresh class for this position
                res = new ClassId(nextId.getAndIncrement());
                classOf.put(new FunctionSymbolReturnType(f), res);
            }

            List<ClassId> args = new ArrayList<>(f.getArity());
            for (int i = 0; i < f.getArity(); ++i) {
                TypePosition argPos = new FunctionSymbolArgumentType(f, i);
                ClassId c = classOf.get(argPos);
                if (c == null) {
                    c = new ClassId(nextId.getAndIncrement());
                    classOf.put(argPos, c);
                }
                args.add(c);
            }

            if (definedSymbols.contains(f)) {
                defSigs.put(f, new DefSig(f, args, res));
            } else {
                ctorSigs.put(f, new CtorSig(f, args, res));
                ctorsByResult.computeIfAbsent(res, k -> new LinkedHashSet<>()).add(f);
            }
        }

        // 4) Build SortInfo map (may include uninhabited sorts; filter if you want to forbid them)
        Map<ClassId, SortInfo> sorts = new LinkedHashMap<>();
        for (ClassId id : new LinkedHashSet<>(classOf.values())) {
            Set<FunctionSymbol> ctors = ctorsByResult.getOrDefault(id, Collections.emptySet());
            sorts.put(id, new SortInfo(id, ctors));
        }

        // 5) Done
        return new TypeEnv(sorts, ctorSigs, defSigs);
    }

}

