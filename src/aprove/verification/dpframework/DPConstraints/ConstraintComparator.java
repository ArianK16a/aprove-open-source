package aprove.verification.dpframework.DPConstraints;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;

/**
 * Compares constraints up to a renaming of their variables: two constraints
 * are equal iff a bijective renaming of the variables maps one to the other.
 */
public class ConstraintComparator implements Comparator<Constraint> {

    /**
     * The renaming built up while two constraints are compared. It is used
     * for the whole constraints, as the scope of a variable is the outermost
     * implication.
     */
    private static class Renaming {
        private final Map<TRSVariable, TRSVariable> forward = new LinkedHashMap<TRSVariable, TRSVariable>();
        private final Map<TRSVariable, TRSVariable> backward = new LinkedHashMap<TRSVariable, TRSVariable>();
    }

    private int getHash(Constraint o) {
        if (o.isPredicate()) {
            return 1;
        }
        if (o.isReducesTo()) {
            return 2;
        }
        if (o.isImplication()) {
            return 3;
        }
        if (o.isConstraintSet()) {
            return 4;
        }
        return 0;
    }

    private int compareSS(ConstraintSet o1, ConstraintSet o2, Renaming map) {
        int h = o1.size() - o2.size();
        if (h == 0) {
            Iterator<Constraint> it1 = o1.iterator();
            Iterator<Constraint> it2 = o2.iterator();
            while (h == 0 && it1.hasNext()) {
                h = this.compareCC(it1.next(), it2.next(), map);
            }
        }
        return h;
    }

    private int compareII(Implication o1, Implication o2, Renaming map) {
        int l = o1.getQuantor().size();
        int h = l - o2.getQuantor().size();
        if (h == 0) {
            h = this.compareSS(o1.getConditions(), o2.getConditions(), map);
        }
        if (h == 0) {
            h = this.compareCC(o1.getConclusion(), o2.getConclusion(), map);
        }
        if (h == 0) {
            // Quantified variables may only be renamed to quantified variables
            for (final TRSVariable v : o1.getQuantor()) {
                final TRSVariable w = map.forward.get(v);
                if (w != null && !o2.getQuantor().contains(w)) {
                    return 1;
                }
            }
            for (final TRSVariable w : o2.getQuantor()) {
                final TRSVariable v = map.backward.get(w);
                if (v != null && !o1.getQuantor().contains(v)) {
                    return -1;
                }
            }
        }
        return h;
    }

    private int compareAA(TermAtom o1, TermAtom o2, Renaming map) {
        int h = this.compareTT(o1.getLeft(), o2.getLeft(), map);
        if (h == 0) {
            h = this.compareTT(o1.getRight(), o2.getRight(), map);
        }
        return h;
    }

    private int compareFF(TRSFunctionApplication o1, TRSFunctionApplication o2, Renaming map) {
        int h = o1.getRootSymbol().hashCode() - o2.getRootSymbol().hashCode();
        for (int i = 0; h == 0 && i < o1.getArguments().size(); i++) {
            h = this.compareTT(o1.getArgument(i), o2.getArgument(i), map);
        }
        return h;
    }

    private int compareTT(TRSTerm o1, TRSTerm o2, Renaming map) {
        if (o1.isVariable() && o2.isVariable()) {
            final TRSVariable v1 = (TRSVariable) o1;
            final TRSVariable v2 = (TRSVariable) o2;
            final TRSVariable image = map.forward.get(v1);
            final TRSVariable preimage = map.backward.get(v2);
            if (image == null && preimage == null) {
                map.forward.put(v1, v2);
                map.backward.put(v2, v1);
                return 0;
            }
            if (v2.equals(image) && v1.equals(preimage)) {
                return 0;
            }
            // The variables are already renamed differently. The result must
            // not be 0, also if v1 and v2 are the same variable.
            if (image != null && !v2.equals(image)) {
                return image.getName().compareTo(v2.getName());
            }
            return v1.getName().compareTo(preimage.getName());
        }
        if (!o1.isVariable() && !o2.isVariable()) {
            return this.compareFF((TRSFunctionApplication) o1, (TRSFunctionApplication) o2, map);
        }
        return o1.isVariable() ? -1 : 1;
    }

    private int compareCC(Constraint o1, Constraint o2, Renaming map) {
        int l = this.getHash(o1);
        int h = l - this.getHash(o2);
        if (h == 0) {
            switch (l) {
            case 1:
            case 2:
                return this.compareAA((TermAtom) o1, (TermAtom) o2, map);
            case 3:
                return this.compareII((Implication) o1, (Implication) o2, map);
            case 4:
                return this.compareSS((ConstraintSet) o1, (ConstraintSet) o2, map);
            default:
                return o1.hashCode() - o2.hashCode();
            }
        }
        return h;
    }

    @Override
    public int compare(Constraint o1, Constraint o2) {
        // System.err.println("1: "+o1);
        // System.err.println("2: "+o2);
        int h = this.compareCC(o1, o2, new Renaming());
        //System.out.println(h);
        return h;

    }

}
