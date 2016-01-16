class kNN {

 var trainSamples: array2 < int > ;
 var testSamples: array2 < int > ;
 var trainClasses: array < int > ;
 var numRows: int;
 var numCols: int;
 var kVal: int; //k value needed for kNN algorithm

 // This predicate express a class invariant: All objects of this calls should satisfy this.
 predicate Valid()
 reads this, this.testSamples, this.trainSamples; {
  testSamples != null && numRows > 0 && numRows == testSamples.Length0 && numCols > 0 && numCols == testSamples.Length1 &&
   trainSamples != null && numRows > 0 && numRows == trainSamples.Length0 && numCols > 0 && numCols == trainSamples.Length1 
   && kVal >= 1 && trainClasses != null && numRows == trainClasses.Length
 }


 method Init(k: int, rows: int, cols: int, trainclasses: array < int >, trainsamples : array2 <int>,testsamples : array2 <int> )
  //Note that Init methods always typically need to state that they will modify this object, as their purpose is to initialise all the fields. 
 modifies this;
 //number of rows and columns must be greater than 0
 requires rows > 0 && cols > 0 && k > 0;
 requires trainclasses != null;
 requires trainsamples != null;
 requires testsamples != null;
 ensures trainSamples != null;
 ensures testSamples != null;
 ensures trainClasses != null;
 requires trainclasses.Length == rows;
 requires trainsamples.Length0 == rows;
 requires testsamples.Length0 == rows;
 requires trainsamples.Length1 == cols;
 requires testsamples.Length1 == cols;
 //make sure initializes numRows and numCols from user input
 ensures numRows == rows;
 ensures numCols == cols;
 //make sure initializes kVal from user input
 ensures kVal == k;
 // ensures trainSamples && trainSamples are newly created object.
 //ensures fresh(trainSamples);
 //ensures fresh(testSamples);
 //ensure row and column length same as user input
 ensures numRows == trainSamples.Length0 && numRows == testSamples.Length0 && numRows == trainClasses.Length;
 ensures numCols == trainSamples.Length1 && numCols == testSamples.Length1; 
 {
  numRows := rows;
  numCols := cols;
  trainClasses := trainclasses;
  trainSamples := trainsamples;//new int[numRows, numCols];
  testSamples := testsamples;//new int[numRows, numCols];
  assert numRows == trainSamples.Length0 && numRows == testSamples.Length0;
  assert numCols == trainSamples.Length1 && numCols == testSamples.Length1;
  kVal := k;
 }

 method classify() returns(assignedTestClass: array < int > )
  //predicate must be valid
 requires this.Valid();
 ensures assignedTestClass != null;
 ensures assignedTestClass.Length == testSamples.Length0;
 //number of rows must be the same for both test and train data
 requires numRows == trainSamples.Length0 && numRows == testSamples.Length0;
 //number of columns must be the same for both test and train data
 requires numCols == trainSamples.Length1 && numCols == testSamples.Length1;
 //make sure predicate is still valid
 ensures this.Valid(); {
  //used to loop through test samples, then train samples
  var testRowNumber := testSamples.Length0;
  var trainRowNumber := trainSamples.Length0;
  assignedTestClass := new int[testSamples.Length0];

  //store both distance and index
  var distances := new real[trainRowNumber, 2];
  var i := 0;
  //initialize distances array to 0.0
  while (i < trainRowNumber)
   invariant 0 <= i <= trainRowNumber;
  invariant forall k: nat::k < i ==> distances[k, 0] == 0.0;
  invariant forall k: nat::k < i ==> distances[k, 1] == 0.0;
  invariant forall k: nat::k < i ==> 0 <= distances[k, 1].Trunc < trainClasses.Length;
  decreases distances.Length0 - i; {
   distances[i, 0] := 0.0; //distance to be stored here
   distances[i, 1] := 0.0; //index to be store here
   i := i + 1;
  }

  i := 0;
  //initialize assignedTestClass array to -1
  while (i < assignedTestClass.Length)
   invariant 0 <= i <= assignedTestClass.Length;
  invariant forall k: nat::k < i ==> assignedTestClass[k] == -1;
  decreases assignedTestClass.Length - i; {
   assignedTestClass[i] := -1; //assigned classes to be stored here
   i := i + 1;
  }
  
  //knn algorithm:
  //for each test sample, calculate its distance to each train sample
  //classify test sample to label of closest train sample

  var tst := 0;
  while (tst < testRowNumber)
   invariant 0 <= tst <= testRowNumber;
  invariant distances != null;
  invariant numRows == distances.Length0 && distances.Length1 == 2;
  invariant testRowNumber == testSamples.Length0;
  invariant trainRowNumber == trainSamples.Length0;

  decreases testRowNumber - tst; {
   var tr := 0;
   var trsample := new real[numCols];
   var tstsample := new real[numCols];
   var dist := 0.0;

   while (tr < trainRowNumber)
    invariant 0 <= tst <= testRowNumber;
   invariant 0 <= tr <= trainRowNumber;
   invariant trsample != null;
   invariant tstsample != null;
   invariant numCols == trsample.Length;
   invariant numCols == tstsample.Length;
   invariant tstsample.Length == trsample.Length;
   invariant trainSamples.Length1 == trsample.Length;
   invariant trsample.Length >= 1;
   invariant tstsample.Length >= 1;
   invariant testRowNumber == testSamples.Length0;
   invariant trainRowNumber == trainSamples.Length0;
   invariant forall k: nat::k < tr ==> 0 <= distances[k, 1].Trunc < trainClasses.Length;
   invariant forall k: nat::k < tr ==> distances[k, 1] == real(k);
   decreases trainRowNumber - tr; {
    // for each test sample, calculate distance from every training sample
    trsample := getRow(tr, true);
    tstsample := getRow(tst, false);

    assert tstsample.Length == trsample.Length; //assert legnth is equal

    dist := getDistance(tstsample, trsample);
    //store distance and training sample index 
    distances[tr, 0] := dist;
    assert distances[tr, 0] == dist;
    distances[tr, 1] := real(tr);

    assert real(tr).Trunc < trainClasses.Length; //assert conversion from real to int doesn't raise issues 

    tr := tr + 1;
   }
   //sort distances and take top K
   //var dupDistances := arrayCopy(distances); //this method call is not necessary since copying is done in selectionsort method
   var i := 0;
   while (i < distances.Length0)
    invariant 0 <= 1 <= distances.Length0; {
    assert distances[i, 1].Trunc < trainClasses.Length;
    assert distances[i, 1].Trunc >= 0;
    i := i + 1;
   }
   var sortedDistances := sort(distances);
   assert sortedDistances.Length0 >= 1;
   assert sortedDistances.Length1 >= 1;
   assert kVal >= 1;

   i := 0;
   while (i < distances.Length0)
    invariant 0 <= 1 <= distances.Length0; {
    assert distances[i, 1].Trunc < trainClasses.Length;
    assert distances[i, 1].Trunc >= 0;
    i := i + 1;
   }

   //if k value is less than the number of training samples then find the top k
   if (kVal < sortedDistances.Length0) {
    assert 0 < kVal < sortedDistances.Length0;
    var topKSortedDistances := arrayCopy(sortedDistances, kVal, sortedDistances.Length1);

    var voteX := 0;
    var voteY := 0;

    var i := 0;
    while (i < topKSortedDistances.Length0)
     invariant 0 <= i <= topKSortedDistances.Length0;
    invariant forall k: nat::k < tr ==> 0 <= distances[k, 1].Trunc < trainClasses.Length; {

     var j := 0;
     while (j < distances.Length0)
      invariant 0 <= 1 <= distances.Length0; {
      assert distances[j, 1].Trunc < trainClasses.Length;
      assert distances[j, 1].Trunc >= 0;
      j := j + 1;
     }

     if (topKSortedDistances[i, 1].Trunc < trainClasses.Length) {
      var rowIndex := getRowIndex(distances, topKSortedDistances[i, 0]);
      if (0 <= rowIndex < trainClasses.Length) {
       assert 0 <= rowIndex < trainClasses.Length;
       if (trainClasses[rowIndex] == 1) {
        voteX := voteX + 1;
       } else {
        voteY := voteY + 1;
       }
      }
     }
     i := i + 1;
    }
    if (voteX > voteY) {
     assignedTestClass[tst] := 1;
     assert voteX > voteY;
    } else {
     assignedTestClass[tst] := 0;
     assert voteX <= voteY;
    }
   }
   tst := tst + 1;
  }

 }


 /**
  ** getRowIndex(...) - obtains and returns row index from 2d array
  ** a : array<real>  - array to obtain row index from
  ** key : real - distance value (or key) used to obtain index from row 
  ** returns rowIndex : int - return rowIndex i.e training sample/row location
  **/
 method getRowIndex(a: array2 < real > , key: real) returns(rowIndex: int)
 requires a != null;
 //ensures a.Length0 >= rowIndex;
 requires a.Length1 == 2;
 requires forall k: nat::k < a.Length0 ==> 0 <= a[k, 1].Trunc < a.Length0;
 ensures 0 <= rowIndex ==> exists k::0 <= k < a.Length0 && a[k, 0] == key;
 ensures 0 > rowIndex ==> forall k::0 <= k < a.Length0 ==> a[k, 0] != key;
 ensures forall k: nat::k < a.Length0 ==> 0 <= a[k, 1].Trunc < a.Length0;
 ensures rowIndex < a.Length0; {
  rowIndex := -1;
  var i := 0;
  while (i < a.Length0)
   invariant 0 <= i <= a.Length0;
  invariant 0 > rowIndex ==> forall k::0 <= k < i ==> a[k, 0] != key;
  invariant 0 <= rowIndex ==> exists k::0 <= k < i && a[k, 0] == key;
  invariant forall k: nat::k < i ==> 0 <= a[k, 1].Trunc < a.Length0; {
   if a[i, 0] == key {
    rowIndex := a[i, 1].Trunc;
    return;
   }
   i := i + 1;
  }
  rowIndex := -1;
 }

 /**
  ** arrayCopy(...) - obtains and returns row data from either training data (true) or test data (false)
  ** rowNum : int - row number of obtain from data
  ** tr : bool - is get row from training data (true) or test data (false)
  ** returns row : array<real> - return row data from either training data (true) or test data (false)
  **/
 method arrayCopy(arr: array2 < real > , len0: int, len1: int) returns(res: array2 < real > )
 requires arr != null;
 ensures res != null;
 requires arr.Length0 >= len0;
 requires arr.Length1 >= len1;
 requires len0 >= 1 && len1 >= 1;
 ensures len0 >= 1 && len1 >= 1;
 ensures len0 == res.Length0;
 ensures len1 == res.Length1;
 //dafny nested quantifier incompleteness
 //ensures forall k : nat :: k < arr.len0 && forall j : nat :: j < arr.len1 ==> arr[k,j] == res[k,j]; 
 {
  res := new real[len0, len1];
  var i := 0;

  while (i < len0)
   invariant 0 <= i <= len0;
  invariant len0 == res.Length0;
  invariant len1 == res.Length1;
  decreases len0 - i; {
   var j := 0;

   while (j < len1)
    invariant 0 <= i <= len0;
   invariant 0 <= j <= len1;
   invariant len0 == res.Length0;
   invariant len1 == res.Length1;
   invariant forall k: nat::k < j ==> arr[i, k] == res[i, k];
   decreases len1 - j; {
    res[i, j] := arr[i, j];
    assert res[i, j] == arr[i, j];
    j := j + 1;
   }
   i := i + 1;
  }
 }



 /**
  ** getRow(...) - obtains and returns row data from either training data (true) or test data (false)
  ** rowNum : int - row number of obtain from data
  ** tr : bool - is get row from training data (true) or test data (false)
  ** returns row : array<real> - return row data from either training data (true) or test data (false)
  **/
 method getRow(rowNum: int, tr: bool) returns(row: array < real > )
  //predicate must be valid
 requires this.Valid();
 //rowNum must be within range of both test and train data
 requires 0 <= rowNum < trainSamples.Length0 && 0 <= rowNum < trainSamples.Length0;
 //number of columns must be the same for both test and train data
 requires numCols == trainSamples.Length1 && numCols == trainSamples.Length1;
 //tr is bool and must be either true or false
 requires tr == true || tr == false;
 //ensure scope of tr never changes
 ensures tr == true || tr == false;
 //make sure predicate is still valid
 ensures this.Valid();
 //make sure returned row is not null
 ensures row != null;
 //the return row data should have the same length as test and train data's column
 ensures row.Length == numCols;
 //if row from training data is request, all cell values in training data matches the returned row data
 ensures forall k: nat::k < numCols && tr ==> row[k] == real(trainSamples[rowNum, k]);
 //if row from test data is request, all cell values in test data matches the returned row data
 ensures forall k: nat::k < numCols && !tr ==> row[k] == real(testSamples[rowNum, k]); {
  row := new real[numCols];
  var i := 0;
  while (i < numCols)
   invariant 0 <= i <= numCols;
  invariant numCols == row.Length;
  invariant numCols == trainSamples.Length1;
  invariant numCols == testSamples.Length1;
  invariant trainSamples.Length1 >= 1;
  invariant testSamples.Length1 >= 1;
  invariant row.Length >= 1;
  invariant forall k: nat::k < i && tr ==> row[k] == real(trainSamples[rowNum, k]);
  invariant forall k: nat::k < i && !tr ==> row[k] == real(testSamples[rowNum, k]);
  decreases numCols - i; {
   if (tr) {
    row[i] := real(trainSamples[rowNum, i]);
   } else {
    row[i] := real(testSamples[rowNum, i]);
   }
   i := i + 1;
  }
 }

 /** 
  ** getDistance(..) - calculates and returns square of Euclidean distance between two vectors
  ** assumes sample1 and sample2 are valid i.e. same length
  ** sample1, sample2: array<real> - array (or vectors) with cell values 
  ** returns distance : real - eculidean distance result
  **/
 method getDistance(sample1: array < real > , sample2: array < real > ) returns(distance: real)
  //sample1 and sample2 must not be null;
 requires sample1 != null && sample2 != null;
 //sample1 and sample2 must have same length
 requires sample1.Length == sample2.Length;
 //predicate must be valid
 requires this.Valid();
 //make sure sample1 and sample2 have same length
 ensures sample1.Length == sample2.Length;
 //make sure predicate is valid
 ensures this.Valid();
 //make sure the distance is correct
 ensures distance == distanceTo(sample1, sample2, sample1.Length); {
  distance := 0.0;
  var i := 0;
  var temp := 0.0;
  while (i < sample1.Length)
   invariant 0 <= i <= sample1.Length;
  decreases sample1.Length - i;
  invariant distance == distanceTo(sample1, sample2, i); {
   temp := sample1[i] - sample2[i];
   distance := distance + (temp * temp);
   i := i + 1;
  }
 }

 /** 
  ** distanceTo(..) - mathematical, recursive definition of the 
  ** distance function from 0 to n-1 over two arrays
  ** it is needed to specify the functionality of the method above
  ** sample1, sample2: array<real> - array (or vectors) with cell values 
  ** real - eculidean distance result
  **/
 function distanceTo(sample1: array < real > , sample2: array < real > , n: int): real
 //sample1 and sample2 must not be null;
 requires sample1 != null && sample2 != null;
 //sample1 and sample2 must have same length
 requires sample1.Length == sample2.Length;
 // index n should be within sample1 and sample2 range
 requires 0 <= n && n <= sample1.Length;
 requires 0 <= n && n <= sample2.Length;
 //make sure sample1 and sample2 have same length
 ensures sample1.Length == sample2.Length;
 decreases n;
 reads sample1, sample2; {
  if (n == 0) then 0.0
  else distanceTo(sample1, sample2, n - 1) + ((sample1[n - 1] - sample2[n - 1]) * (sample1[n - 1] - sample2[n - 1]))
 }


 predicate sorted(a: array2 < real > , lo: int, hi: int)
 requires a != null;
 requires a.Length1 == 2;
 //requires 0 <= i <= a.Length0;
 reads a; {
  forall j, k::0 <= lo <= j < k < hi <= a.Length0 ==> a[j, 0] <= a[k, 0]
 }

 method sort(a: array2 < real > ) returns(res: array2 < real > )
 requires a != null;
 requires a.Length0 >= 1;
 requires a.Length1 == 2;
 requires forall k: nat::k < a.Length0 ==> a[k, 1].Trunc <= a.Length0;
 ensures res != null;
 ensures res.Length1 == 2;
 ensures sorted(res, 0, res.Length0);
 ensures res.Length0 >= 1;
 ensures res.Length0 == a.Length0;
 ensures res.Length1 == a.Length1;
 //ensures forall k : nat :: k < res.Length0 ==> res[k,1].Trunc <= res.Length0; 
 {
  //res := arrayCopy(a, a.Length0, a.Length1);

  //create copy of arr to res
  res := new real[a.Length0, a.Length1];
  //initialize res array to 0.0
  var i: int;
  i := 0;
  while (i < res.Length0)
   invariant 0 <= i <= res.Length0;
  invariant forall k: nat::k < i ==> res[k, 0] == 0.0;
  invariant forall k: nat::k < i ==> res[k, 1] == 0.0;
  invariant forall k: nat::k < i ==> res[k, 1].Trunc <= res.Length0;
  decreases res.Length0 - i; {
   res[i, 0] := 0.0; //distance to be stored here
   res[i, 1] := 0.0; //index to be store here
   i := i + 1;
  }

  i := 0;
  while (i < res.Length0)
   invariant 0 <= i <= res.Length0;
  invariant a.Length0 == res.Length0;
  invariant a.Length1 == res.Length1;
  invariant forall k: nat::k < i && res[k, 0] != 0.0 ==> a[k, 0] == res[k, 0];
  invariant forall k: nat::k < i && res[k, 1] != 0.0 ==> a[k, 1] == res[k, 1];
  invariant forall k: nat::k < i ==> a[k, 1].Trunc <= a.Length0;
  invariant forall k: nat::k < i ==> res[k, 1].Trunc <= res.Length0;
  decreases res.Length0 - i; {
   var j := 0;

   while (j < res.Length1)
    invariant 0 <= i <= res.Length0;
   invariant 0 <= j <= res.Length1;
   invariant a.Length0 == res.Length0;
   invariant a.Length1 == res.Length1;
   invariant forall k: nat::k < i && res[k, 0] != 0.0 ==> a[k, 0] == res[k, 0];
   invariant forall k: nat::k < i && res[k, 1] != 0.0 ==> a[k, 1] == res[k, 1];
   invariant forall k: nat::k < j ==> a[i, k] == res[i, k];
   invariant forall k: nat::k < j ==> a[i, 1].Trunc <= res.Length0;
   invariant forall k: nat::k < j && a[i, k].Trunc <= res.Length0 ==> res[i, k].Trunc <= res.Length0;
   decreases res.Length1 - j; {
    res[i, j] := a[i, j];
    assert res[i, j] == a[i, j];
    if (j == 1) {
     assert res[i, 1] == a[i, 1];
     assert res[i, 1].Trunc <= res.Length0;
     assert a[i, 1].Trunc <= a.Length0;
    }
    j := j + 1;
   }
   i := i + 1;
  }

  assert res != null;
  assert res.Length0 == a.Length0;
  assert res.Length1 == a.Length1;


  //if (res.Length0 == 0) { return; } //remove because requires Length0 >= 1
  i := 0;
  while (i < res.Length0)
   invariant 0 <= i <= res.Length0
  invariant a.Length0 == res.Length0;
  invariant a.Length1 == res.Length1;
  invariant forall j::0 <= j < i <= res.Length0 ==> res[0, 0] <= res[j, 0];
  invariant forall k: nat::k < i && res[k, 0] < res[0, 0] && res[0, 1].Trunc <= res.Length0 ==> res[k, 1].Trunc <= res.Length0;
  //invariant forall j :: 0 <= j < i < res.Length0 ==> res[i,1].Trunc <= res.Length0;
  invariant forall k: nat::k < i ==> a[k, 1].Trunc <= res.Length0;
  //invariant forall k : nat :: k < i ==> res[k,1].Trunc <= res.Length0;
  decreases res.Length0 - i; {
   if (res[i, 0] < res[0, 0]) {
    res[0, 0], res[i, 0] := res[i, 0], res[0, 0];
    res[0, 1], res[i, 1] := res[i, 1], res[0, 1];
   }
   i := i + 1;
  }
  i := 1;
  while (i < res.Length0)
   invariant 0 < i <= res.Length0;
  invariant a.Length0 == res.Length0;
  invariant a.Length1 == res.Length1;
  invariant sorted(res, 0, i);
  invariant forall j::0 <= j < res.Length0 ==> res[0, 0] <= res[j, 0];
  invariant forall k: nat::k < i && res[k, 0] < res[0, 0] && res[0, 1].Trunc <= res.Length0 ==> res[k, 1].Trunc <= res.Length0;
  //invariant forall j :: 0 <= j < res.Length0 ==> res[j,1].Trunc <= res.Length0;
  decreases res.Length0 - i; {
   var j: int := i;
   var v: real := res[i, 0];
   var v1: real := res[i, 1];
   while (v < res[j - 1, 0])
    decreases j;
   invariant res[0, 0] <= v;
   invariant 0 < j <= i;
   invariant a.Length0 == res.Length0;
   invariant a.Length1 == res.Length1;
   invariant sorted(res, j, i + 1);
   invariant forall k::0 <= k < a.Length0 ==> res[0, 0] <= res[k, 0];
   invariant forall k::j <= k <= i ==> v <= res[k, 0];
   //invariant forall k : nat :: k < i && res[k,0] < res[0,0] && res[0,1].Trunc <= res.Length0 ==> res[k,1].Trunc <= res.Length0;
   invariant forall k: nat::0 < k < j < i && res[i, 0] < res[k, 0] && res[k, 1].Trunc <= res.Length0 ==> res[i, 1].Trunc <= res.Length0;
   //invariant forall j, k :: 0 <= 0 <= j < k < i <= res.Length0 ==> res[k,1].Trunc <= res.Length0;
   invariant sorted(res, 0, i); {
    res[j, 0] := res[j - 1, 0];
    res[j, 1] := res[j - 1, 1];
    j := j - 1;
   }
   res[j, 0] := v;
   res[j, 1] := v1;
   i := i + 1;
  }
 }


 /**
  ** adapted from Yonatan Biri- Selection Sort verification http://rise4fun.com/Dafny/OB
  **/

 method SelectionSort(arr: array2 < real > ) returns(res: array2 < real > )
 requires arr != null;
 requires arr.Length1 == 2;
 requires arr.Length0 >= 1;
 //does not modify arr, instead creates a copy to res
 //modifies arr;
 ensures res != null;
 ensures res.Length1 == 2;
 ensures res.Length0 >= 1;
 ensures sortedUp(res, res.Length0);
 ensures res.Length0 == arr.Length0;
 ensures res.Length1 == arr.Length1; {
  //local var
  var j, iMin := 0,
   0;
  assert j == iMin;
  //create copy of arr to res
  res := new real[arr.Length0, arr.Length1];
  var i := 0;
  while (i < arr.Length0)
   invariant 0 <= i <= arr.Length0;
  invariant arr.Length0 == res.Length0;
  invariant arr.Length1 == res.Length1;
  decreases arr.Length0 - i; {
   var j := 0;

   while (j < arr.Length1)
    invariant 0 <= i <= arr.Length0;
   invariant 0 <= j <= arr.Length1;
   invariant arr.Length0 == res.Length0;
   invariant arr.Length1 == res.Length1;
   invariant forall k: nat::k < j ==> arr[i, k] == res[i, k];
   decreases arr.Length1 - j; {
    res[i, j] := arr[i, j];
    assert res[i, j] == arr[i, j];
    j := j + 1;
   }
   i := i + 1;
  }

  assert res != null;
  assert res.Length0 == arr.Length0;
  assert res.Length1 == arr.Length1;
  //sort based on column index 0 (distance)
  while (j < res.Length0)
   invariant 0 <= j <= res.Length0 && j - 1 <= iMin <= res.Length0;
  invariant forall k::0 <= k < j < arr.Length0 ==> res[k, 0] <= res[j, 0]; //from 0 to j all elements are small than j
  invariant forall k::0 <= k < j < arr.Length0 ==> sortedUp(res, k); //from 0 to j all elements are sorted up
  invariant forall k::0 < j < k < res.Length0 ==> res[k, 0] >= res[j - 1, 0]; //from j to n all elements are bigger then j-1
  invariant forall k1, k2::0 <= k1 < j <= k2 < arr.Length0 ==> res[k1, 0] <= res[k2, 0]; //the elements in the "sorted" part of the array are smaller than the elements in the "unsorted" array
  invariant sortedUp(res, j);
  decreases res.Length0 - j; {
   assert 0 <= j <= res.Length0;
   assert j - 1 <= iMin <= res.Length0;
   assert forall k::0 <= k < j < arr.Length0 ==> res[k, 0] <= res[j, 0];
   assert forall k::0 <= k < j < arr.Length0 ==> sortedUp(res, k);
   assert forall k::0 < j < k < res.Length0 ==> res[k, 0] >= res[j - 1, 0];
   assert forall k1, k2::0 <= k1 < j <= k2 < arr.Length0 ==> res[k1, 0] <= res[k2, 0];
   assert sortedUp(res, j);
   iMin := Min(res, j);
   assert j - 1 <= iMin <= res.Length0;
   assert forall k::j <= k < res.Length0 ==> res[k, 0] >= res[iMin, 0]; //arr[iMin] is the minimal in arr[j-n]
   assert forall k::0 <= k < j ==> res[k, 0] <= res[iMin, 0]; //all elements in arr[0-j] are smaller the arr[iMin]
   //swap - local var used
   //swap for column index 0 (distances) and column index 1 (trainNumber)
   var resJ := res[j, 0];
   var resI := res[iMin, 0];
   var resJ1 := res[j, 1];
   var resI1 := res[iMin, 1];
   assert resJ == res[j, 0] && resI == res[iMin, 0];
   assert resJ1 == res[j, 1] && resI1 == res[iMin, 1];
   res[j, 0] := resI;
   res[iMin, 0] := resJ;
   res[j, 1] := resI1;
   res[iMin, 1] := resJ1;
   assert res[j, 0] == resI && res[iMin, 0] == resJ;
   assert res[j, 1] == resI1 && res[iMin, 1] == resJ1;
   assert forall k::0 <= k < j < arr.Length0 ==> res[k, 0] <= res[j, 0];
   assert forall k::0 <= k < j < arr.Length0 ==> sortedUp(res, k);
   assert forall k::0 < j < k < res.Length0 ==> res[k, 0] >= res[j - 1, 0];
   assert forall k1, k2::0 <= k1 < j <= k2 < arr.Length0 ==> res[k1, 0] <= res[k2, 0];
   j := j + 1;
   assert j + 1 < res.Length0 ==> res[j - 1, 0] <= res[j, 0];
   assert forall k::0 < k < j - 1 ==> res[k, 0] <= res[j - 1, 0];
   assert j + 1 < res.Length0 ==> forall k::0 <= k < j ==> res[k, 0] <= res[j, 0];
   assert j + 1 < res.Length0 ==> sortedUp(res, j - 1);
   assert j + 1 == res.Length0 ==> sortedUp(res, j);
  }
  assert res != null;
  assert sortedUp(res, res.Length0);
  assert res.Length0 == arr.Length0;
 }

 //Predicates
 //Sorted Array
 predicate sortedUp(arr: array2 < real > , i: int)
 requires arr != null;
 requires arr.Length1 == 2;
 requires 0 <= i <= arr.Length0;
 reads arr; //as I am using array
 {
  forall k::0 < k < i ==> arr[k - 1, 0] <= arr[k, 0]
 }

 //Minimum Index == Min Element in the array
 predicate MinIndex(arr: array2 < real > , i: int)
 requires arr != null;
 requires arr.Length1 == 2;
 requires 0 <= i < arr.Length0;
 reads arr; //as I am using array
 {
  forall k::i <= k < arr.Length0 ==> arr[k, 0] >= arr[i, 0]
 }

 //Helper Methods
 //this menthod finds the minimal value in arr[i..n] - the "unsorted" half
 method Min(arr: array2 < real > , i: int) returns(iMin: int)
 requires arr != null;
 requires arr.Length1 == 2;
 requires 0 <= i < arr.Length0;
 ensures i <= iMin < arr.Length0;
 ensures forall k::i <= k < arr.Length0 ==> arr[k, 0] >= arr[iMin, 0];
 ensures MinIndex(arr, iMin); {
  //local var
  assert 0 <= i < arr.Length0;
  var j := i;
  assert j == i && 0 <= j < arr.Length0;
  //start iMin to be the first element in the "unsorted" array
  iMin := i;
  assert iMin == i && iMin == j && 0 <= iMin < arr.Length0;
  //iterate up, keeping i=< j <= arr.Length && MinIndex(arr, iMin) is true at the end of each iteration.
  while (j < arr.Length0)
   invariant i <= j <= arr.Length0;
  invariant i <= iMin < arr.Length0;
  invariant forall k::i <= k < j ==> arr[k, 0] >= arr[iMin, 0];
  decreases arr.Length0 - j; {
   //cases of arr[iMin]
   if {
    case arr[j, 0] < arr[iMin, 0] => {
     assert i <= j <= arr.Length0;
     assert i <= iMin < arr.Length0;
     assert forall k::i <= k < j ==> arr[k, 0] >= arr[iMin, 0];
     assert forall k::i <= k < j ==> arr[k, 0] >= arr[j, 0];
     iMin := j;
     assert iMin == j && arr[j, 0] == arr[iMin, 0];
     assert arr[j, 0] >= arr[iMin, 0];
     assert forall k::i <= k <= j ==> arr[k, 0] >= arr[iMin, 0];
    }
    case arr[j, 0] >= arr[iMin, 0] => {
     assert i <= j <= arr.Length0;
     assert i <= iMin < arr.Length0;
     assert forall k::i <= k < j ==> arr[k, 0] >= arr[iMin, 0];
     assert forall k::i <= k <= j ==> arr[k, 0] >= arr[iMin, 0];
    }
   }
   assert arr[j, 0] >= arr[iMin, 0];
   assert forall k::i <= k <= j ==> arr[k, 0] >= arr[iMin, 0];
   assert i <= j < arr.Length0;
   j := j + 1; //iteration
   assert i <= j <= arr.Length0;
  }
  assert i <= iMin < arr.Length0;
  assert forall k::i <= k < arr.Length0 ==> arr[k, 0] >= arr[iMin, 0];
  assert MinIndex(arr, iMin);
 }

}

method	Main()
{
  var testCase1 := new kNN;
  
  //CASE 1 - 2 ROWS 2 COLUMNS WITH INPUT DATA 
  // EXPECTED OUTPUT SHOULD BE EITHER 0 OR 1
  var trainClasses := new int[2];
  trainClasses[0] := 0;
  trainClasses[1] := 1;
  
  var trainSamples := new int[2,2];
  trainSamples[0,0] := 1;
  trainSamples[0,1] := 0;
  trainSamples[1,0] := 0;
  trainSamples[1,1] := 1;
  
  var testSamples := new int[2,2];
  testSamples[0,0] := 1;
  testSamples[0,1] := 0;
  testSamples[1,0] := 0;
  testSamples[1,1] := 1;
  
  assert trainSamples.Length0 == testSamples.Length0;
  assert trainSamples.Length1 == testSamples.Length1;
  testCase1.Init(2, 2, 2, trainClasses, trainSamples,testSamples);
  
  var result := testCase1.classify();
  
  //assert result[0] == -1 || result[0]>= 0;
  
  
  
  
  
}
