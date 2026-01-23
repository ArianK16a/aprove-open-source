package aprove.verification.dpframework.IDPProblem.utility;

import java.math.*;
import java.util.*;
import java.util.concurrent.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.PredefinedFunction.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.domains.*;
import aprove.verification.dpframework.Utility.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 *
 * @author Martin Pluecker
 */
public class IDPPredefinedMap implements Exportable, NameProvider {

    public static final IDPPredefinedMap EMPTY_MAP = new IDPPredefinedMap(ImmutableCreator.create(Collections
        .<FunctionSymbol, PredefinedFunction<? extends Domain>>emptyMap()), Collections.<String>emptySet());
    public static final IDPPredefinedMap DEFAULT_MAP;
    static {
        final Set<Domain> defaultDomains = Collection_Util.<Domain>createConcurrentHashSet();
        defaultDomains.add(DomainFactory.INTEGERS);
        defaultDomains.add(DomainFactory.BOOLEAN);
        DEFAULT_MAP =
            new IDPPredefinedMap(
                ImmutableCreator.create(Collections.<FunctionSymbol, PredefinedFunction<? extends Domain>>emptyMap()),
                defaultDomains,
                Collections.<String>emptySet());
    }

    protected final Map<FunctionSymbol, PredefinedConstructor> constructors;

    protected final ImmutableMap<FunctionSymbol, PredefinedFunction<? extends Domain>> mapping;
    protected final Set<Domain> usedDomains;
    protected final ImmutableMap<ImmutablePair<Func, List<? extends Domain>>, FunctionSymbol> reverseMapping;
    protected final Set<String> fsNames;

    public IDPPredefinedMap(
        final ImmutableMap<FunctionSymbol, PredefinedFunction<? extends Domain>> mapping,
        final Collection<String> usedFunctionSymboldNames)
    {
        this(mapping, Collection_Util.<Domain>createConcurrentHashSet(), usedFunctionSymboldNames);
    }

    protected IDPPredefinedMap(
        final ImmutableMap<FunctionSymbol, PredefinedFunction<? extends Domain>> mapping,
        final Set<Domain> usedDomains,
        final Collection<String> usedFunctionSymboldNames)
    {
        this.constructors = new LinkedHashMap<FunctionSymbol, PredefinedConstructor>();
        final Map<FunctionSymbol, PredefinedFunction<? extends Domain>> completedMapping =
            new ConcurrentHashMap<FunctionSymbol, PredefinedFunction<? extends Domain>>(mapping);
        final Map<ImmutablePair<Func, List<? extends Domain>>, FunctionSymbol> reverse =
            new ConcurrentHashMap<ImmutablePair<Func, List<? extends Domain>>, FunctionSymbol>();

        this.usedDomains = usedDomains;
        this.fsNames = Collection_Util.<String>createConcurrentHashSet();
        // reverse mapping and collect used domains
        for (final Map.Entry<FunctionSymbol, PredefinedFunction<? extends Domain>> entry : completedMapping.entrySet())
        {
            final ImmutablePair<Func, List<? extends Domain>> key =
                new ImmutablePair<Func, List<? extends Domain>>(entry.getValue().getFunc(), entry
                    .getValue()
                    .getDomains());
            if (reverse.containsKey(key)) {
                throw new IllegalArgumentException("dupplicate predefeind semantics: "
                    + entry.getKey()
                    + " and "
                    + reverse.get(key));
            }
            reverse.put(key, entry.getKey());
            this.fsNames.add(entry.getKey().getName());
            usedDomains.addAll(entry.getValue().getDomains());
            usedDomains.add(entry.getValue().getResultDomain());
        }

        // complete mapping
        final FreshNameGenerator freshNames =
            new FreshNameGenerator(usedFunctionSymboldNames, FreshNameGenerator.APPEND_NUMBERS);
        final Collection<PredefinedFunction<? extends Domain>> allFunctions =
            PredefinedSemanticsFactory.getAllFunctions(usedDomains);
        for (final PredefinedFunction<? extends Domain> func : allFunctions) {
            final ImmutablePair<Func, List<? extends Domain>> key =
                new ImmutablePair<Func, List<? extends Domain>>(func.getFunc(), func.getDomains());
            if (!reverse.containsKey(key)) {
                final StringBuilder name = new StringBuilder();
                name.append(func.getFunc().getName());
                final ImmutableList<? extends Domain> doms = func.getDomains();
                boolean allIntegerDomains = true;
                boolean allBooleanDomains = true;
                for (final Domain dom : doms) {
                    if (dom.isBooleanDomain()) {
                        allIntegerDomains = false;
                    } else if (dom.isIntegerDomain()) {
                        allBooleanDomains = false;
                        if (!DomainFactory.INTEGERS.equals(dom)) {
                            allIntegerDomains = false;
                            break;
                        }
                    }
                }
                if (!allIntegerDomains && !allBooleanDomains) {
                    for (final Domain dom : doms) {
                        name.append(DomainFactory.SUFFIX_SEPERATOR);
                        name.append(dom.getSuffix());
                    }
                }
                final FunctionSymbol fs;
                if (usedFunctionSymboldNames.isEmpty()) {
                    fs = FunctionSymbol.create(name.toString(), func.getArity());
                } else {
                    fs = FunctionSymbol.create(freshNames.getFreshName(name.toString(), false), func.getArity());
                }
                this.fsNames.add(fs.getName());
                reverse.put(new ImmutablePair<Func, List<? extends Domain>>(func.getFunc(), doms), fs);
                completedMapping.put(fs, func);
            }
        }

        this.reverseMapping = ImmutableCreator.create(reverse);
        this.mapping = ImmutableCreator.create(completedMapping);
    }

    public PredefinedSemantics getPredefinedSemantics(final FunctionSymbol fs) {
        final PredefinedSemantics func = this.mapping.get(fs);
        if (func == null) {
            synchronized (this.constructors) {
                if (this.constructors.containsKey(fs)) {
                    return this.constructors.get(fs);
                }
                for (final Domain dom : this.usedDomains) {
                    final PredefinedConstructor sem = PredefinedSemanticsFactory.getConstructor(dom, fs);
                    if (sem != null) {
                        this.constructors.put(fs, sem);
                        return sem;
                    }
                }
                this.constructors.put(fs, null);
            }
        } else {
            return func;
        }
        return null;
    }

    public PredefinedFunction<? extends Domain> getPredefinedFunction(final FunctionSymbol fs) {
        return this.mapping.get(fs);
    }

    public ImmutableMap<FunctionSymbol, PredefinedFunction<? extends Domain>> getMapping() {
        return this.mapping;
    }

    public boolean isPredefined(final FunctionSymbol fs) {
        return this.getPredefinedSemantics(fs) != null;
    }

    public boolean isPredefinedFunction(final FunctionSymbol fs) {
        final PredefinedFunction<? extends Domain> func = this.getPredefinedFunction(fs);
        return func != null;
    }

    public boolean isDivOrMod(final FunctionSymbol fs) {
        final PredefinedFunction<? extends Domain> func = this.getPredefinedFunction(fs);
        return func != null && (func.getFunc() == Func.Div || func.getFunc() == Func.Mod);
    }

    public boolean isAdd(final FunctionSymbol fs) {
        final PredefinedFunction<? extends Domain> func = this.getPredefinedFunction(fs);
        return func != null && func.getFunc() == Func.Add;
    }

    public boolean isSub(final FunctionSymbol fs) {
        final PredefinedFunction<? extends Domain> func = this.getPredefinedFunction(fs);
        return func != null && func.getFunc() == Func.Sub;
    }

    public boolean isUnaryMinus(final FunctionSymbol fs) {
        final PredefinedFunction<? extends Domain> func = this.getPredefinedFunction(fs);
        return func != null && func.getFunc() == Func.UnaryMinus;
    }

    public boolean isMul(final FunctionSymbol fs) {
        final PredefinedFunction<? extends Domain> func = this.getPredefinedFunction(fs);
        return func != null && func.getFunc() == Func.Mul;
    }

    public boolean isDiv(final FunctionSymbol fs) {
        final PredefinedFunction<? extends Domain> func = this.getPredefinedFunction(fs);
        return func != null && func.getFunc() == Func.Div;
    }

    public boolean isMod(final FunctionSymbol fs) {
        final PredefinedFunction<? extends Domain> func = this.getPredefinedFunction(fs);
        return func != null && func.getFunc() == Func.Mod;
    }

    /**
     * Checks whether a function symbol is a predefined arithmetic function,
     * i.e. all it's arguments are integers and the return type is integer.
     * @param fs Function symbol to check
     * @return
     */
    public boolean isArithmeticFunction(final FunctionSymbol fs) {
        return IDPPredefinedMap.DEFAULT_MAP.isAdd(fs)
               || IDPPredefinedMap.DEFAULT_MAP.isSub(fs)
               || IDPPredefinedMap.DEFAULT_MAP.isUnaryMinus(fs)
               || IDPPredefinedMap.DEFAULT_MAP.isMul(fs)
               || IDPPredefinedMap.DEFAULT_MAP.isDiv(fs)
               || IDPPredefinedMap.DEFAULT_MAP.isMod(fs);
    }

    public boolean isLand(final FunctionSymbol fs) {
        final PredefinedFunction<? extends Domain> func = this.getPredefinedFunction(fs);
        return func != null && func.getFunc() == Func.Land;
    }

    public boolean isLor(final FunctionSymbol fs) {
        final PredefinedFunction<? extends Domain> func = this.getPredefinedFunction(fs);
        return func != null && func.getFunc() == Func.Lor;
    }

    public boolean isLnot(final FunctionSymbol fs) {
        final PredefinedFunction<? extends Domain> func = this.getPredefinedFunction(fs);
        return func != null && func.getFunc() == Func.Lnot;
    }

    public boolean isEq(final FunctionSymbol fs) {
        final PredefinedFunction<? extends Domain> func = this.getPredefinedFunction(fs);
        return func != null && func.getFunc() == Func.Eq;
    }

    public boolean isNeq(final FunctionSymbol fs) {
        final PredefinedFunction<? extends Domain> func = this.getPredefinedFunction(fs);
        return func != null && func.getFunc() == Func.Neq;
    }

    public boolean isLt(final FunctionSymbol fs) {
        final PredefinedFunction<? extends Domain> func = this.getPredefinedFunction(fs);
        return func != null && func.getFunc() == Func.Lt;
    }

    public boolean isLe(final FunctionSymbol fs) {
        final PredefinedFunction<? extends Domain> func = this.getPredefinedFunction(fs);
        return func != null && func.getFunc() == Func.Le;
    }

    public boolean isGt(final FunctionSymbol fs) {
        final PredefinedFunction<? extends Domain> func = this.getPredefinedFunction(fs);
        return func != null && func.getFunc() == Func.Gt;
    }

    public boolean isGe(final FunctionSymbol fs) {
        final PredefinedFunction<? extends Domain> func = this.getPredefinedFunction(fs);
        return func != null && func.getFunc() == Func.Ge;
    }


    /**
     * Checks whether a function symbol is a predefined relation on integers,
     * i.e. all it's arguments are integers and the return type is boolean.
     * @param fs Function symbol to check
     * @return
     */
    public boolean isIntegerRelation(final FunctionSymbol fs) {
        return IDPPredefinedMap.DEFAULT_MAP.isLt(fs)
               || IDPPredefinedMap.DEFAULT_MAP.isLe(fs)
               || IDPPredefinedMap.DEFAULT_MAP.isGt(fs)
               || IDPPredefinedMap.DEFAULT_MAP.isGe(fs);
    }

    public boolean isInt(final FunctionSymbol fs, final IntegerDomain domain) {
        return PredefinedSemanticsFactory.getIntValue(fs, domain) != null;
    }

    public BigInteger getInt(final FunctionSymbol fs, final IntegerDomain domain) {
        return PredefinedSemanticsFactory.getIntValue(fs, domain);
    }

    public PfInt getInt(final BigIntImmutable value, final IntegerDomain domain) {
        return PredefinedSemanticsFactory.getInt(value, domain);
    }

    public TRSFunctionApplication getIntTerm(final BigIntImmutable value, final IntegerDomain domain) {
        return PredefinedSemanticsFactory.getIntTerm(value, domain);
    }

    public FunctionSymbol getIntSym(final BigIntImmutable value, final IntegerDomain domain) {
        return PredefinedSemanticsFactory.getIntSym(value, domain);
    }

    public PfBoolean getBooleanTrue() {
        if (this.usedDomains.contains(DomainFactory.BOOLEAN)) {
            return PredefinedSemanticsFactory.BOOLEAN_TRUE;
        } else {
            return null;
        }
    }

    public PfBoolean getBooleanFalse() {
        if (this.usedDomains.contains(DomainFactory.BOOLEAN)) {
            return PredefinedSemanticsFactory.BOOLEAN_FALSE;
        } else {
            return null;
        }
    }

    public boolean isBooleanTrue(final FunctionSymbol fs) {
        return PredefinedSemanticsFactory.BOOLEAN_FS_TRUE.equals(fs)
            && this.usedDomains.contains(DomainFactory.BOOLEAN);
    }

    public boolean isBooleanFalse(final FunctionSymbol fs) {
        return PredefinedSemanticsFactory.BOOLEAN_FS_FALSE.equals(fs)
            && this.usedDomains.contains(DomainFactory.BOOLEAN);
    }

    public <D extends Domain> FunctionSymbol getSym(final Func func, final D domain) {
        final ArrayList<D> domains = new ArrayList<D>(func.getArity());
        for (int i = func.getArity(); i > 0; i--) {
            domains.add(domain);
        }
        return this.reverseMapping.get(new ImmutablePair<Func, List<D>>(func, domains));
    }

    public <D extends Domain> FunctionSymbol getSym(final Func func, final List<D> dom) {
        return this.reverseMapping.get(new ImmutablePair<Func, List<D>>(func, dom));
    }

    public FunctionSymbol getSym(final Func func, final Domain... domains) {
        return this.reverseMapping.get(new ImmutablePair<Func, List<? extends Domain>>(func, Arrays.asList(domains)));
    }

    public ImmutableCollection<FunctionSymbol> getPredefinedFunctionSymbols() {
        return ImmutableCreator.create(this.mapping.keySet());
    }

    @Override
    public String export(final Export_Util o) {
        return this.export(null, o);
    }

    public String export(final Collection<FunctionSymbol> usedSymbols, final Export_Util o) {
        final StringBuilder sb = new StringBuilder();
        sb.append(o.tableStart(3));
        for (final Map.Entry<FunctionSymbol, PredefinedFunction<? extends Domain>> entry : this.mapping.entrySet()) {
            if (usedSymbols == null || usedSymbols.contains(entry.getKey())) {
                final ArrayList<String> row = new ArrayList<String>(4);
                row.add(entry.getKey().export(o));
                row.add("~");
                row.add(entry.getValue().export(o));
                sb.append(o.tableRow(row));
            }
        }
        sb.append(o.tableEnd());
        return sb.toString();
    }

    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }

    public boolean isUndefinedInt(final FunctionSymbol fs) {
        final PredefinedSemantics sem = this.getPredefinedSemantics(fs);
        return sem != null && sem.isConstructor() && sem instanceof PfUndefinedInt;
    }

    @Override
    public boolean contains(final String name) {
        if (this.fsNames.contains(name)) {
            return true;
        }
        if (this.usedDomains.contains(DomainFactory.BOOLEAN)) {
            if (PredefinedSemanticsFactory.BOOLEAN_FS_FALSE.getName().equals(name)
                || PredefinedSemanticsFactory.BOOLEAN_FS_TRUE.getName().equals(name))
            {
                return true;
            }
        }
        if (name.matches("-?\\d+")) {
            final BigInteger value = new BigInteger(name);
            for (final Domain dom : this.usedDomains) {
                if (dom.isIntegerDomain()) {
                    final IntegerDomain iDom = (IntegerDomain) dom;
                    if (iDom.inRange(value)) {
                        return true;
                    }
                }
            }
        }
        return false;
    }

    /**
     * If the provided symbol {@code fs} is an infix symbol (with two arguments) and has some Left-To-Right
     * precedence, return its precedence. Otherwise return null;
     * @param fs The function symbol to check.
     * @return The precedence of fs or null.
     */
    public Integer getInfixLTRPrecedence(final FunctionSymbol fs) {
        // Precendence rules (from grammar):
        // 9: (expr) left-to-right (!!)
        // 8: !, - (unary) right-to-left (!!)
        // 7: *,/,% left-to-right
        // 6: +, - left-to-right
        // 5: <,<=,=,>=,> left-to-right
        // 4: | left-to-right
        // 3: ^ left-to-right
        // 2: & left-to-right
        // 1: || left-to-right
        // 0: && left-to-right
        if (fs.getArity() != 2) {
            return null;
        }
        final PredefinedFunction<? extends Domain> func = this.getPredefinedFunction(fs);
        if (func == null) {
            return null;
        }
        switch (func.getFunc()) {
        case Land:
            return 0;
        case Lor:
            return 1;
        case Bwand:
            return 2;
        case Bwxor:
            return 3;
        case Bwor:
            return 4;
        case Add:
            return 6;
        case Sub:
            return 6;
        case Mul:
            return 7;
        case Div:
            return 7;
        case Mod:
            return 7;
        case Gt:
            return 5;
        case Ge:
            return 5;
        case Eq:
            return 5;
        case Neq:
            return 5;
        case Le:
            return 5;
        case Lt:
            return 5;
        default:
            return null;
        }
    }

    /**
     * @return a set that contains the function symbol names explicitly stored
     *  in this IDPPredefinedMap; result may be modified
     */
    public Set<String> getUsedNames() {
        final Set<String> res = new LinkedHashSet<String>(this.mapping.size() * 4 / 3 + 1);
        for (final FunctionSymbol f : this.mapping.keySet()) {
            res.add(f.getName());
        }
        return res;
    }
}
