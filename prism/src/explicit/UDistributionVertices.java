package explicit;

import common.Interval;
import common.iterable.Reducible;
//import org.apache.commons.lang3.NotImplementedException;

import java.util.*;

public class UDistributionVertices<Value> implements UDistribution<Value>{


    int[] support;
    HashSet<Integer> supportSet;
    public double [][] vertices;
    public List<List<Interval<Value>>> marginals;
    public double [][][] marginalVertices;

    protected int smartThreshholdMarginal = 20000;
    protected int smartThreshholdProduct = 20000;
    public boolean smartSuccess = true;

    public UDistributionVertices (List<List<Interval<Value>>> marginals, List<Integer> support) {
        this.support = support.stream().mapToInt(Integer::intValue).toArray();
        this.supportSet = new HashSet<>(support);
        this.marginals = marginals;
        //System.out.println("Support: " + Arrays.toString(this.support) + " Marginals: " + marginals);

        buildVertices(false);
        System.out.println("Num Vertices: " + vertices.length + " - Early stop: " + !smartSuccess);
    }

    public UDistributionVertices (List<List<Interval<Value>>> marginals, List<Integer> support, boolean smart) {
        this.support = support.stream().mapToInt(Integer::intValue).toArray();
        this.supportSet = new HashSet<>(support);
        this.marginals = marginals;
        //System.out.println("Support: " + Arrays.toString(this.support) + " Marginals: " + marginals);

        buildVertices(smart);
        System.out.println("Num Vertices: " + vertices.length + " - Early stop: " + !smartSuccess);
    }

    public UDistributionVertices (List<List<Interval<Value>>> marginals, int[] support, boolean smart) {
        this.support = support;
        supportSet = new HashSet<>();
        for (int i : support) {
            supportSet.add(i);
        }
        this.marginals = marginals;
        //System.out.println("Support: " + Arrays.toString(this.support) + " Marginals: " + marginals);

        buildVertices(smart);
        //System.out.println("Num Vertices: " + vertices.length + " - Early stop: " + !smartSuccess);
    }

    public UDistributionVertices(int[] support, double[][] vertices) {
        this.support = support;
        this.vertices = vertices;

        // Build support hashset for efficient lookup
        supportSet = new HashSet<>();
        for (int i : support) {
            supportSet.add(i);
        }
        this.marginalVertices=null;
    }




    protected void buildVertices(boolean smart){
        this.marginalVertices = enumerateVerticesFromMarginals(this.marginals, smart);
//        System.out.println("Vertices:");
//        for (double[][] v : marginalVertices) {
//            System.out.print("[");
//            for(double[] row : v){
//                System.out.print(Arrays.toString(row));
//            }
//            System.out.print("]");
//            System.out.println("");
//        }
//        System.out.println("");
////
//        System.out.println("Product Vertices:");
        if (smart && !smartSuccess) {
            this.vertices = new double[0][0];
            return;
        }
        this.vertices = multiplyMarginalVertices(this.marginalVertices);
//        for (double[] row : this.vertices) {
//            System.out.println("Row: " + Arrays.toString(row));
//        }
    }

    /**
     * Computes the vertex product over all marginal vertices.
     * @param marginalVertices a 3D array where marginalVertices[i] is a 2D array containing the vertices for the i-th marginal.
     * @return a 2D array of product vertices, where each row is the product vertex computed for one combination from the Cartesian product of the marginals.
     */
    public static double[][] multiplyMarginalVertices(double[][][] marginalVertices) {
        if (marginalVertices == null || marginalVertices.length == 0) {
            return new double[0][];
        }

        // Initialize the result list with the vertices from the first marginal.
        List<double[]> productList = new ArrayList<>(Arrays.asList(marginalVertices[0]));

        // Iteratively combine with vertices from the remaining marginals.
        for (int i = 1; i < marginalVertices.length; i++) {
            List<double[]> newProductList = new ArrayList<>();
            // For each already computed product vertex...
            for (double[] currentProduct : productList) {
                // ... multiply with every vertex in the current marginal.
                for (double[] vertex : marginalVertices[i]) {
                    // Compute the outer product of the current product and the new vertex.
                    double[] combined = outerMultiply(currentProduct, vertex);
                    newProductList.add(combined);
                }
            }
            // Update the product list with the newly computed products.
            productList = newProductList;
        }

        // Convert the list of product vertices into a 2D array.
        return productList.toArray(new double[productList.size()][]);
    }


    /**
     * Enumerates the vertices of interval box intersected with simplex.
     * For dimensions d>=2, it fixes d-1 coordinates (each at either its lower or upper bound)
     * and computes the remaining coordinate so that the sum equals 1.
     *
     * @param intervals A list of Interval objects defining the bounds for each coordinate.
     * @param smart Whether to stop at exceeding given smart threshold
     * @return A two-dimensional array of doubles where each row is a vertex.
     */
    public double[][] enumerateVertices(List<Interval<Value>> intervals, boolean smart) {
        int d = intervals.size();
        double tol = 1e-9;  // Tolerance for floating point comparisons
        List<double[]> vertices = new ArrayList<>();

        // Special case: dimension 1.
        if (d == 1) {
            if ((double) intervals.get(0).getLower() <= 1.0 && 1.0 <= (double) intervals.get(0).getUpper()) {
                vertices.add(new double[]{1.0});
            }
            return vertices.toArray(new double[vertices.size()][]);
        }

        // For each coordinate, treat it as the free coordinate.
        // The fixed coordinates are all other indices.
        for (int freeIndex = 0; freeIndex < d; freeIndex++) {
            // Build a list of indices for the fixed coordinates.
            List<Integer> fixedIndices = new ArrayList<>();
            for (int j = 0; j < d; j++) {
                if (j != freeIndex) {
                    fixedIndices.add(j);
                }
            }
            int numFixed = fixedIndices.size(); // equals d-1
            // There are 2^(d-1) ways to assign lower/upper bounds to these fixed coordinates.
            int totalCombinations = 1 << numFixed;  // 2^(d-1)
            for (int comb = 0; comb < totalCombinations; comb++) {
                double[] vertex = new double[d];
                double sumFixed = 0.0;
                // For each fixed coordinate, decide whether to use its lower or upper bound.
                for (int j = 0; j < numFixed; j++) {
                    int idx = fixedIndices.get(j);
                    // Check the j-th bit of comb: if 0, choose lower; if 1, choose upper.
                    double value = ((comb >> j) & 1) == 0 ? (double) intervals.get(idx).getLower() : (double) intervals.get(idx).getUpper();
                    vertex[idx] = value;
                    sumFixed += value;
                }
                // Solve for the free coordinate.
                vertex[freeIndex] = 1.0 - sumFixed;

                // Check if the free coordinate lies within its interval bounds (with tolerance).
                if (vertex[freeIndex] >= (double) intervals.get(freeIndex).getLower() - tol &&
                        vertex[freeIndex] <= (double) intervals.get(freeIndex).getUpper() + tol) {
                    // Avoid adding duplicate vertices (within tolerance).
                    boolean unique = true;
                    for (double[] v : vertices) {
                        if (areClose(v, vertex, tol)) {
                            unique = false;
                            break;
                        }
                    }
                    if (unique) {
                        vertices.add(vertex);
                        if (vertices.size() > smartThreshholdMarginal && smart) {
                            smartSuccess = false;
                            return vertices.toArray(new double[vertices.size()][]);
                        }
                    }
                }
            }
        }
        return vertices.toArray(new double[vertices.size()][]);
    }

    /**
     * Given a list of interval boxes (each represented as a list of Interval objects),
     * enumerates the vertices for each box and collects them into a single two-dimensional array.
     *
     * @param marginals A list of boxes, where each box is defined by a list of Interval objects.
     * @return A two-dimensional array containing all vertices from all boxes.
     */
    public double[][][] enumerateVerticesFromMarginals(List<List<Interval<Value>>> marginals, boolean smart) {
        List<double[][]> allVertices = new ArrayList<>();
        int prod = 1;
        for (List<Interval<Value>> box : marginals) {
            double[][] vertices = enumerateVertices(box, smart);
            allVertices.add(vertices);
            prod *= vertices.length;
            if (prod > smartThreshholdProduct && smart) {
                this.smartSuccess = false;
                break;
            }
        }
        return allVertices.toArray(new double[allVertices.size()][][]);
    }

    /**
     * Helper function to check if two vectors are element-wise approximately equal
     * within a given tolerance.
     *
     * @param a   The first vector.
     * @param b   The second vector.
     * @param tol The tolerance for the comparison.
     * @return true if the vectors are approximately equal, false otherwise.
     */
    private boolean areClose(double[] a, double[] b, double tol) {
        if (a.length != b.length) {
            return false;
        }
        for (int i = 0; i < a.length; i++) {
            if (Math.abs(a[i] - b[i]) > tol) {
                return false;
            }
        }
        return true;
    }

    @Override
    public boolean contains(int j)
    {
        return supportSet.contains(j);
    }

    @Override
    public boolean isSubsetOf(BitSet set) {
        return Reducible.extend(getSupport()).allMatch(set::get);
    }

    @Override
    public boolean containsOneOf(BitSet set)
    {
        return Reducible.extend(getSupport()).anyMatch(set::get);
    }

    @Override
    public Set<Integer> getSupport()
    {
        return supportSet;
    }

    @Override
    public boolean isEmpty()
    {
        return support.length == 0;
    }

    @Override
    public int size()
    {
        return support.length;
    }

    /**
     * Do a single row of matrix-vector multiplication followed by min/max,
     * i.e. return min/max_P { sum_j P(s,j)*vect[j] }
     * @param vect Vector to multiply by
     * @param minMax Min/max uncertainty (via isMinUnc/isMaxUnc)
     */
    @Override
    public double mvMultUnc(double[] vect, MinMax minMax)
    {
        // Get relevant entries
        double[] vectProj = new double[support.length];
        for (int i = 0; i < vectProj.length; i++) {
            vectProj[i] = vect[support[i]];
        }

        if(vertices.length == 0) {
            System.out.println("No vertices found: Marginals: "+ marginals);
        }

        double opt = innerMultiply(vectProj, vertices[0]);

        for (int i = 1; i < vertices.length; i++) {
            double res = innerMultiply(vectProj, vertices[i]);
            opt = minMax.isMinUnc() ? Math.min(opt, res) : Math.max(opt, res);
        }

        return opt;
    }

    /**
     * Computes the outer product multiplication between two vectors.
     * @param v1 the first vector
     * @param v2 the second vector
     * @return a new vector representing the outer product of v1 and v2
     */
    public static double[] outerMultiply(double[] v1, double[] v2) {
        int len1 = v1.length;
        int len2 = v2.length;
        double[] result = new double[len1 * len2];
        for (int i = 0; i < len2; i++) {
            double multiplier = v2[i];
            int offset = i * len1;
            for (int j = 0; j < len1; j++) {
                result[offset + j] = multiplier * v1[j];
            }
        }
        return result;
    }

    /**
     * Computes the inner product multiplication between two vectors.
     * @param v1 the first vector
     * @param v2 the second vector
     * @return the inner product
     */
    public static double innerMultiply(double[] v1, double[] v2) {
        assert v1.length == v2.length;
        int len = v1.length;
        double result = 0.0;

        //System.out.println("V1: " + Arrays.toString(v1) + " V2: " + Arrays.toString(v2));
        for (int i = 0; i < len; i++) {
            result += v1[i] * v2[i];
        }

        return result;
    }

    @Override
    public UDistributionVertices<Value> copy()
    {
        return new UDistributionVertices<>(support.clone(), vertices.clone());
    }

    @Override
    public UDistributionVertices<Value> copy(int[] permut)
    {

        //TODO::
        // Permute support
        int[] supportPerm = new int[support.length];
        for (int i = 0; i < support.length; i++) {
            supportPerm[i] = support[permut[i]];
        }

        // Permute vertices
        double[][] verticesPerm = new double[vertices.length][];
        for (int i = 0; i < vertices.length; i++) {
            for (int j = 0; j < vertices[i].length; j++) {
                verticesPerm[i][j] = vertices[i][permut[j]];
            }
        }

        UDistributionVertices<Value> newDist = new UDistributionVertices<Value>(supportPerm, verticesPerm);
        //throw new NotImplementedException("Not yet implemented.");
        throw new UnsupportedOperationException("Not yet implemented.");
    }

    @Override
    public String toString()
    {
        String s = "Vertices, ";
        s += "Support: " + Arrays.stream(support)
                .boxed()
                .toList();
        s += " ";
        s += "Vertices: " + vertices.length + "]";//Arrays.deepToString(vertices);
        return s;
    }

}

