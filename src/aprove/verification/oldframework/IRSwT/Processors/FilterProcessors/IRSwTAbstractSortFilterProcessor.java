package aprove.verification.oldframework.IRSwT.Processors.FilterProcessors;

import java.util.*;

import org.w3c.dom.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.oldframework.IRSwT.Filters.*;
import aprove.verification.oldframework.IRSwT.Sorts.*;
import aprove.verification.oldframework.IntTRS.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.xml.*;
import immutables.*;

/**
 * Filters away term- or mixed-sorted arguments.
 * @author Matthias Hoelzel
 */
public abstract class IRSwTAbstractSortFilterProcessor extends Processor.ProcessorSkeleton {
    /** Arguments that can be passed to this processor. */
    public class Arguments {
        /**
         * If set to true, this processor will be unsuccessful when
         * it filters something. Useful for checking whether or not
         * any integers/terms are occurring.
         * Default: false.
         */
        boolean noSuccIfChanged;

        /**
         * Ensures that every variable from the right side also occurs at the left side.
         */
        boolean filterFreeVariables;
    }

    /** Arguments. */
    private final Arguments args;

    /** Constructor! */
    public IRSwTAbstractSortFilterProcessor() {
        this.args = new Arguments();
    }

    /**
     * Setter for argument noSuccIfChanged
     * @param value boolean
     */
    public void setNoSuccIfChanged(final boolean value) {
        this.args.noSuccIfChanged = value;
    }

    /**
     * Setter for argument filterFreeVariables
     * @param value boolean
     */
    public void setFilterFreeVariables(final boolean value) {
        this.args.filterFreeVariables = value;
    }

    @Override
    public boolean isApplicable(final BasicObligation obl) {
        return obl instanceof IRSwTProblem && !((IRSwTProblem) obl).isBounded();
    }

    @Override
    public Result process(
        final BasicObligation obl,
        final BasicObligationNode oblNode,
        final Abortion aborter,
        final RuntimeInformation rti) throws AbortionException
    {
        assert obl instanceof IRSwTProblem : "Wrong obligation!";
        final IRSwTProblem irswt = (IRSwTProblem) obl;

        // 1. Deduce the sorts
        final SortAnalyzer sortAnalyzer = new SortAnalyzer(irswt.getRules());
        final SortDictionary sorts = sortAnalyzer.analyze();

        // 2. Apply filter:
        final AbstractFilter filter = this.createFilter(irswt, sorts);
        final LinkedHashSet<IGeneralizedRule> filteredRules = filter.applyFilter();

        final LinkedHashSet<IGeneralizedRule> newRules;
        if (this.args.filterFreeVariables) {
            final AbstractFilter freeVarFilter = new FreeVarFilter(filteredRules);
            newRules = freeVarFilter.applyFilter();
        } else {
            newRules = filteredRules;
        }

        final IRSwTProblem newProblem;
        if (filter instanceof RemoveTermFilter || filter instanceof RetainIntFilter) {
            newProblem = new IRSProblem(ImmutableCreator.create(newRules), irswt.getStartTerm());
        } else {
            newProblem = new IRSwTProblem(ImmutableCreator.create(newRules), irswt.getStartTerm());
        }

        if (this.args.noSuccIfChanged && filter.hasChanged()) {
            return ResultFactory.unsuccessful();
        }

        final YNMImplication impl;
        if (filter.hasChanged()) {
            impl = YNMImplication.SOUND;
        } else {
            impl = YNMImplication.EQUIVALENT;
        }
        // Finally we return everything:
        return ResultFactory.proved(newProblem, impl, new FilterProof(filter, sorts, irswt));
    }

    /**
     * Creates a filter.
     * @param irswt current problem
     * @param dict a sort dicitonary
     * @return an abstract filter
     */
    protected abstract AbstractFilter createFilter(IRSwTProblem irswt, SortDictionary dict);

    /**
     * A truly gruesome proof!
     * @author Matthias Hoelzel
     */
    class FilterProof extends DefaultProof {
        /** Stores the filter we applied. */
        private final AbstractFilter filter;

        /** Some sort dictionary. */
        private final SortDictionary sortDict;
        
        private final IRSLike origProb;


        /**
         * Constructor!
         * @param abstractFilter the applied filter
         * @param sortDictionary some sort dictionary
         */
        public FilterProof(final AbstractFilter abstractFilter, final SortDictionary sortDictionary, IRSLike origProb) {
            this.filter = abstractFilter;
            this.sortDict = sortDictionary;
            this.origProb = origProb;
        }

        @Override
        public String export(final Export_Util eu, final VerbosityLevel level) {
            final StringBuilder sb = new StringBuilder();
            sb.append(eu.tttext("Used the following sort dictionary for filtering: "));
            sb.append(this.sortDict.export(eu));
            sb.append(eu.linebreak());
            sb.append(this.filter.export(eu));
            return sb.toString();
        }
        
        @Override
        public Element toCPF(final Document doc, final Element[] childrenProofs, final XMLMetaData xmlMetaData, final CPFModus modus) {
            return childrenProofs[0];
        }

        @Override
        public boolean isCPFCheckableProof(final CPFModus modus) {
            return modus.isPositive();
        }
        
        @Override
        public XMLMetaData adaptMetaData(final XMLMetaData xmlPreMetaData) {
            Map<IGeneralizedRule,IGeneralizedRule> oldNew = new HashMap<>();
            for (IGeneralizedRule rule : this.origProb.getRules()) {
                oldNew.put(rule, this.filter.getNewRule(rule));
            }
            return xmlPreMetaData.adjustOldNew(oldNew).integrateFilter(this.filter);
        }

    }
}
