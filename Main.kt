import kotlin.math.log2
import kotlin.math.roundToInt
import kotlin.random.Random
import kotlin.system.measureTimeMillis

/*
Helper class that supports
- Precalculating all modular inverses in mod n, in O(n)
- Convenience function to calculate sum, subtract, multipy and divide in mod n, using Kotlin's Context objec
 */

class Field(val p:Int){
    /*
    In each of the function (and everywhere in the code), an element mod p is always represented by
    some value in range [0,p-1], all parameters and return values must follow this rule.
     */

    //addition mod p. Modular Plus
    infix fun Int.mp(other:Int):Int {
        val ans = this + other
        return if(ans >= p) ans - p else ans
    }

    //Take x, return -x (mod p)
    fun Int.additiveInverse():Int{
        return if(this == 0) 0 else p-this
    }
    //subtraction mod p. Modular Subtraction
    infix fun Int.ms(other:Int):Int{
        val ans = this - other
        return if(ans < 0) ans + p else ans
    }
    //multiplication mod p. Modular Multiplication
    infix fun Int.mm(other:Int):Int{
        return ((this.toLong() * other) % p ).toInt()
    }
    val inv:IntArray
    init{
        assert((2 until p).all { p % it != 0 }) //assert p is prime
        inv = IntArray(p)
        inv[0] = -1 // Should not be accessed
        inv[1] = 1
        for(i in 2 until p){
            inv[i] = ((p/i) mm inv[p % i]).additiveInverse()
        }
        //O(n) algorithim to get all inverses
    }

    //Make an integer within [-p,2p) fit inside [0,p) range
    fun Int.reduce():Int{
        return if(this >= p) this -p
        else if(this < 0) this + p
        else this
    }

    //division mod p , other must not be 0
    infix fun Int.modDivide(other:Int):Int{
        return this mm (inv[other])
    }
}

/* A simple double linked list implementation, supports:
- Iteration
- Add/Remove any element
- find any element
all values must be within [0,n),

If the set is updated during iteration, the iterator must also be updated

The set initializes as empty.
 */
class LinkedSet(val n:Int){
    // -1 will always denote the either ends of the list
    var size = 0

    val next:IntArray = IntArray(n){-1}
    val previous:IntArray = IntArray(n){-1}
    val present = BooleanArray(n)
    var head = -1

    fun add(x:Int){
        if(present[x]) return
        present[x] = true
        size ++
        val y = head
        next[x] = y
        head = x
        if(y != -1) previous[y] = x
        previous[x] = -1
    }
    fun remove(x:Int){
        if(!present[x]) return
        present[x] = false
        size--
        val w = previous[x]
        val y = next[x]
        if(w == -1){
            head = y
        }else{
            next[w] =y
        }
        if(y != -1){
            previous[y] = w
        }
    }
    //Return any element in the set, or -1 if there is none
    fun first():Int{
        return head
    }

    fun next(iterator:Int):Int{
        return next[iterator]
    }
}
/*
The main function to call

Parameters:
    n : the parameter of n in EGZ theorem. We assume n <= 1e9 so no overflow occurs.
    x: an array of length 2*n-1, each value must be in [0,n-1]
EGZ_prime additionally requires n to be prime
Return:
    A boolean array of size 2*n-1, with exactly n True.
    Sum of the corresponding elements will be a multiple of n
 */
fun EGZ_general(n:Int, x:IntArray):BooleanArray{
    assert(x.size == 2 * n -1)
    assert(x.all { it in 0 until n })
    if(n == 1){
        return booleanArrayOf(true) // when n=1, taking the only element is the only option
    }
    val a = (2..n).first{n % it == 0}
    if(a == n){
        //n is prime
        return EGZ_prime(n, x)
    }
    val b = n/ a

    val remain = ArrayDeque<Int>()
    for(i in x.indices){
        remain.add(i)
    }
    val reconstruct = mutableListOf<IntArray>()
    val B = mutableListOf<Int>()
    while(remain.size >= 2 * a - 1){
        val takeIndex = mutableListOf<Int>()
        repeat(2 * a-1){
            takeIndex.add(remain.removeLast())
        }
        val takeValue = IntArray(2 * a - 1){x[takeIndex[it]] % a}
        val keep = EGZ_general(a, takeValue) // Solve for n=a
        //Bookkeeping to prepare for calls for B
        val localReconstruct = mutableListOf<Int>()
        var localsum = 0
        for(i in keep.indices){
            if(keep[i]){
                localsum += x[takeIndex[i]] //We need the values before mod a, so cannot just use takeValue
                if(localsum >= n) localsum -= n
                localReconstruct.add(takeIndex[i])
            }else{
                remain.add(takeIndex[i])
            }
        }
        reconstruct.add(localReconstruct.toIntArray())
        B.add(localsum / a)
    }

    val keep = EGZ_general(b, B.toIntArray())   // Solve for n=b
    val ret = BooleanArray(2 * n - 1)
    for(i in keep.indices){
        if(keep[i]){
            for(c in reconstruct[i]){
                ret[c] = true
            }
        }
    }

    //Validating the output
    assert(ret.count { it } == n)
    run{
        var finalsum = 0
        for(i in ret.indices){
            if(ret[i]) finalsum += x[i]
            if(finalsum >= n) finalsum -= n
        }
        assert(finalsum == 0)
    }
    return ret
}
/*
max: 1 larger than the maximum value found in x

return:
    a (sortedIndex, sortedValue) pair

runs in O(max + x.size)
 */
fun countingSort(max:Int,x:IntArray):Pair<IntArray,IntArray>{
    val freq = IntArray(max)
    for(a in x){ freq[a] ++}
    //(Stable) Counting Sort
    val sortedValue = IntArray(x.size){-1}
    val sortedIndex = IntArray(x.size){-1}
    for(i in 1 until max){
        freq[i] += freq[i-1]
    }
    for(i in x.lastIndex downTo 0){
        val v = x[i]
        val pos = --freq[v]
        sortedValue[pos] = v
        sortedIndex[pos] = i
    }
    return sortedIndex to sortedValue
}

fun EGZ_prime(n:Int, x:IntArray):BooleanArray{
    assert((2 until n).all { n % it != 0 }) // n is a prime
    assert(x.all { it in 0 until n })
    assert(x.size == 2 * n - 1)

    val (sortedIndex,sortedValue) = countingSort(n,x)

    //Check for n equal values
    for(i in 0 until n-1){
        if(sortedValue[i] == sortedValue[i+n]){
            val ret = BooleanArray(2 * n - 1)
            for(j in i until i+n){
                ret[sortedIndex[j]] = true
            }
            return ret
        }
    }

    val prepareValues = IntArray(n-1){ sortedValue[it + n] - sortedValue[it]}

    //tar is -(sum a_i) for i from 0 until n
    var tar = 0
    for(i in 0 until n){
        tar += sortedValue[i]
        if(tar >= n) tar -= n
    }
    if(tar != 0) tar = n-tar // taking additive inverse of tar

    val take = packingLemma(n,tar,prepareValues) // invoke main lemma

    val ret_aftersort = BooleanArray(2 * n - 1)
    for(i in 0 until n) ret_aftersort[i] = true
    for(i in take.indices){
        if(take[i]){
            ret_aftersort[i] = false
            ret_aftersort[i+n] = true
        }
    }

    //Undo the sorting
    val ret = BooleanArray(2 * n - 1)
    for(i in ret_aftersort.indices){
        if(ret_aftersort[i]){
            ret[sortedIndex[i]] = true
        }
    }


    //Validating output
    assert(ret.count { it } == n)
    run{
        var localsum =0
        for(i in x.indices){
            if(ret[i]){
                localsum += x[i]
                if(localsum >= n ) localsum -= n
            }
        }
        assert(localsum == 0)
    }

    return ret
}

/*
p must be prime, given n-1 nonzero values mod p, find any subset that sums to the given k.
Corresponding to the critical main lemma in the article
 */

class operation(val a:Int, val y:Int, val b:Int, val x:Int, val c:Int, val olda:Int, val oldb:Int){
    /*

    olda = the previous value of A[a]
    oldb = the previous value of A[b]
    an operation having ay=bx
    we had replaced cx copies of b with cy copies of a
     */
}
fun packingLemma(n:Int, k:Int, x:IntArray):BooleanArray {
    assert((2 until n).all { n % it != 0 }) // n is prime
    assert(k in 0 until n)
    assert(x.size == n - 1)
    assert(x.all { it in 1 until n }) // all values must be nonzero, different from the other functions
    if(k == 0){
        return BooleanArray(n-1) // take empty set if target is 0
    }

    val field = Field(n)
    val A = IntArray(n)
    for(a in x) {
        A[a]++
    }

    with(field) {
        //Part I of the algorithm
        val S = LinkedSet(n) // Stores values for which A[i] >= t, the current phase
        val ops = mutableListOf<operation>()
        for(i in 0 until n) {
            if(A[i] > 0) {
                S.add(i)
            }
        }
        var W = n - 1L
        val c = (log2(n.toDouble())).roundToInt() + 1  // Taking c = log n
        val visited = IntArray(n){-1}
        val explorelen = IntArray(n){0} // largest multiple of x that is currently being marked


        //Part I terminates when W >= 2 * n  and c phases are completed
        //Edge case: also terminates if n-1 phases are completed, as this necessarily means A[i] >= n-1 for some i
        overall@for(t in 1 until n) {
            //For simplicity, we only check for termination at start of phase. This adds at most O(n) time to the process
            if(W >= 2 * n && t > c){
                break
            }
            var iterator = S.first()
            while(iterator != -1) {
                val a = iterator
                iterator = S.next(iterator)

                if(A[a] < t){
                    S.remove(a)
                    continue
                }

                val go = t mm a
                if(visited[go] != -1){
                    val b = visited[go]
                    val s = go modDivide b
                    //at = bs
                    assert(t > s)
                    val performCount = A[b] / s
                    val newop = operation(a,t,b,s,performCount,A[a], A[b])
                    ops.add(newop)


                    //simply maintain W as sum of array A
                    W -= A[a]
                    W -= A[b]

                    A[b] -= s * performCount
                    //unmark relevant cells of b
                    for(t in explorelen[b] downTo A[b]+1){
                        visited[t mm b] = -1
                    }
                    explorelen[b] = A[b]

                    //Early breaks when anything reaches n-1, in order to prevent overflow
                    val newa = minOf(n-1L, A[a] + t.toLong() * performCount).toInt()
                    A[a] = newa

                    W += A[a]
                    W += A[b]

                    if(A[a] == n-1){
                        break@overall
                    }
                }
                visited[go] = a

                explorelen[a] = t

            }
        }
        var construct:IntArray? = null

        for(x in 1 until n){
            //If the element can be constructed from single AP, this happens in one of two cases
            // (1) W = p-1 but the algorithim terminated, so every cell is explored
            // (2) Through some value i reaching A[i] = p-1
            val needcopies = k modDivide x
            if(needcopies <= A[x]){
                construct = IntArray(n)
                construct[x] = needcopies
                break
            }
        }
        if(construct == null){
            // The typical case: the conditions are satisfied to have only n/log n APS that can sum to n
            construct = lemma_Part_2(n, k, A)
        }

        //Undoing the operations by modifying the construct
        for(op in ops.reversed()){
            val a = op.a
            val b = op.b
            val convertcount = minOf(construct[a] / op.y,  op.c)
            construct[a] -= op.y * convertcount
            construct[b] += op.x * convertcount

            A[a] = op.olda
            A[b] = op.oldb
        }



        //Converting the frequency array back to a boolean "Take or not" array
        val ret = BooleanArray(x.size)
        for(i in x.indices) {
            val v = x[i]
            if(construct[v] > 0) {
                construct[v]--
                ret[i] = true
            }
        }

        // Validating output
        with(field) {
            var ans = 0
            for(i in ret.indices) {
                if(ret[i]) {
                    ans = ans mp x[i]
                }
            }
            assert(ans == k)
        }

        return ret
    }
}

/*
Parameters
n: must be prime
k: target of sum
A: all values between 0 and n-1
the sum of A must be at least n-1

Return value:
An Intarray ret that satisfies ret[i] <= A[i] for each i, and that sum of i * ret[i] is tar.

Unlike in the article, the function simply packs from the longest chains down to the shortest
The function in part 1 should guarantee this is only called when the sum of n/log n chains already give n-1
 */

fun lemma_Part_2(n:Int, k:Int, A:IntArray):IntArray {

    assert((2 until n).all { n % it != 0 }) // n is prime
    assert(k in 0 until n)
    assert(A.size == n )
    assert(A.all { it in 0 until n })
    assert(A[0] == 0)

    val field = Field(n)
    val parentEdge = IntArray(n){-1} // stores which value marked a certain value
    parentEdge[0] = 0

    val B = LinkedSet(n)
    val BC = LinkedSet(n) // complements of B

    B.add(0)
    for(i in 1 until n) BC.add(i)


    with(field) {
        val (sortedIndex, sortedValue) = countingSort(n, A)
        for(sortedPos in n - 1 downTo 0) {
            val len = sortedValue[sortedPos]
            val v = sortedIndex[sortedPos]
            var take = minOf(n - B.size, len)

            //exactly the check function found in the article
            //however, x and y can be upto 2n
            fun convert(x:Int):Int = (x.reduce() mm v) // undo the coding of multiplying by v^-1
            fun notContain(x:Int):Boolean = parentEdge[convert(x)] == -1 // check if B does not contain x
            fun insert(x:Int){
                val actual = convert(x)
                B.add(actual)
                BC.remove(actual)
                parentEdge[actual] = v
                take --
            }
            fun check(x:Int, y:Int) {
                if(take == 0) return
                if(x+1 == y){
                    insert(y)
                    return
                }
                val mid = (x+y) ushr 1  //unsigned shift right, avoiding a typical overflow in binary search
                if(notContain(mid)){
                    check(x,mid)
                }
                if(notContain(y-1)){
                    check(mid,y-1)
                }
                if(take != 0) {
                    insert(y)
                }
            }
            while(take > 0) {
                var x = B.first() modDivide v
                var y = BC.first() modDivide v
                if(y < x) y += n //Represent x,y such that x < y, thus easy to calculate mid

                check(x,y)
            }
            if(B.size == n){
                break
            }
        }

        //Recovering the answer
        val ret = IntArray(n)
        var tar = k
        while(tar != 0){
            val v = parentEdge[tar]
            ret[v] ++
            tar = tar ms v
        }

        //validating output
        var ansnow = 0
        for(i in 0 until n){
            assert(ret[i] <= A[i])
            ansnow = ansnow mp (ret[i] mm i)
        }
        assert(ansnow == k)
        return ret
    }
}


/*
Testing functions for the theorem
 */
fun generateRandomTest(n:Int):IntArray {
    val values = IntArray(2 * n - 1){ Random.nextInt(n)}
    return values
}

/*
Run for all possible cases for this n
 */
fun testAllCases(n:Int){
    val current = IntArray(2 * n - 1)
    while(true){
        EGZ_general(n,current)

        //Find the lexicographically next test
        for(i in current.lastIndex downTo 0){
            if(current[i] != n-1){
                current[i]++
                break
            }else{
                current[i] = 0
                //All arrays examined
                if(i == 0) return

            }
        }
    }
}

fun testAllSmallN(){
    for(n in 1..5){
        testAllCases(n)
    }
    println("All Tests for small n Passed")
}

//
fun testBigRandomCase(){
    val n = 10_000_169
    val time = measureTimeMillis {
        val p = n
        val t = generateRandomTest(p)
        val ans = EGZ_general(p, t)
    }
    println("Random test on $n, Time: $time ms")
}
fun performRandomTests(){
    repeat(10000){
        val n = 1+Random.nextInt(1000)
        val test = generateRandomTest(n)
        val ans = EGZ_general(n,test)
    }
    println("All Random Tests Passed")
}


fun interactive(){
    val n = readLine()!!.toInt()
    val line = readLine()!!.split(" ").filter { it.isNotBlank() }.map { it.toInt() }
    require(line.size == 2* n - 1){ "There must be exactly 2*n-1 integers"}
    require(line.all { it in 0 until n } ){"All values must be between 0 and n-1"}
    val ans = EGZ_general(n, line.toIntArray())

    println("Solution to EGZ:")
    println((ans.indices).filter { ans[it] }.map { line[it] }.joinToString(" "))
}

//All functions included validation of output.
//Successful execution without RuntimeErrors means the test is solved correctly
fun main(){
    testAllSmallN()
    performRandomTests()
    testBigRandomCase()
    println("Begin interaction:")
    while(true){
        /*
        Read in n from stdin
        then 2*n-1 integers in the next line, space separated
         */
        interactive()
    }
}
