/*********************************************
 * OPL 12.6.1.0 Model
 * Author: Javier Perez
 * Creation Date: 13/05/2019 at 00:00:00
 *********************************************/
//using CP;
// PARAMETROS
 
// NUM_CIUDADES nos da el numero de poblaciones en un territorio
int NUM_CIUDADES = ...;
// El subindice i y el conjunto I se refieren a las localizaciones de las poblaciones.
range I = 1..NUM_CIUDADES;

// NUM_ANTENAS nos da el numero de antenas en un territorio
int NUM_ANTENAS = ...;
// El subindice j y el conjunto J se refieren a las localizaciones de las antenas.
// El subindice l, que se mueve en el conjunto J, 
// se refiere a las posibles antenas a reforzar.
range J = 1..NUM_ANTENAS;

// p: numero total de antenas a reforzar
int p = ...;

// w_i: numero de clientes en la poblacion i.
int w[I] = ...;

// c_j: coste de reforzar la torre j. No se usa en esta version.

// q_l: probabilidad de fallo de la antena reforzada en la localizacion l.
// int q[J] = ...; // = 1/p

// M_j: conjunto de antenas, k, cercanas a la antena j.
// Se considera que dos antenas estan cerca si su distancia es <= 5.92 km.
// Este valor se parametriza en el tratamiento previo de los datos.
{int} M[j in J] = ...;

// N_i: conjunto de antenas j que cubren la poblacion i
// p.ejemplo:
//   N[1] = {10 83 84} 
//   N[2] = {} 
//   N[3] = {3 4 5 17}
{int} N[i in I] = ...;
// Hay un bug en CPLEX 12.6 https://www-01.ibm.com/support/docview.wss?uid=swg1RS02892
// no se puede usar el operador "not in". 
// Por tanto genero tambien el conjunto complementario
{int} NOT_N[i in I] = ...;

// tuplas de indices
// i_l
tuple site_i_antenna_l {int i; int l;}
setof(site_i_antenna_l) i_l = {<i,l> | i in I, l in J};


// VARIABLES
// y_j, binaria, = 1; si la antena en la localizacion j esta reforzada
//				0 en caso contrario
dvar boolean y[J];
// x_i, binaria, = 1; Si la poblacion i esta cubierta por alguna antena
//				0 en caso contrario
dvar boolean x[I];
// z_il, binaria, = 1; si la poblacion i esta cubierta incluso aunque la antena l sea destruida
//				0 en caso contrario
dvar boolean z[i_l];

// v_l Numero total de clientes sin conexion si la antena l es destruida.
dvar int v_l[J];

// Variable si se elige la segunda funcion objetivo: perdiendo
// una sola de las antenas reforzadas. Se pierde la que da 
// cobertura a mas clientes
// En el peor de los escenarios la maxima cantidad de 
// clientes perdida se expresa como se expresa como 
// v = v_l = max_l{v_l}
// v, expresa la maxima perdida de clientes en caso de desastre.
dvar int v; // s:t: v >= v_l forall l;

/*****************************************************************************
 * MODELO
 *****************************************************************************/

// 1. Primera posible funcion objetivo:
// Se maximiza la cobertura de la poblacion total
maximize sum (i in I) w[i] * x[i];

// 2. Segunda posible funcion objetivo:
// Tambien se maximiza la cobertura de la poblacion total,
// pero considerando el peor caso: que se pierde la antena con mayor cobertura
// maximize sum (i in I) (w[i] * x[i]) - v;

// 3. Tercera posible funcion objetivo:
// Tambien se maximiza la cobertura de la poblacion total,
// pero considerando el caso de perdida intermedia
// maximize sum (i in I) w[i] * x[i] - (sum (l in J) v_l[l])/p;
subject to {
	// 4. Fija el numero de antenas a reforzar
	sum (j in J) y[j] == p;
	
	//5. Se define al nodo i como cubierto solo si el sitio 
	// esta cubierto por al menos una antena.
	forall (i in I) x[i] <= sum (j in N[i]) y[j];
	
	// 6.a. Se consideran todos los pares de poblaciones i 
	// y de potenciales antenas reforzadas antenas $l$.
	forall (i in I, l in N[i]) z[<i,l>] <= 1 - 2 * y[l] + sum (j in N[i]) y[j];
	
	// 6.b. Si el nodo l no cubre la poblacion i 
	// entonces su destruccion no le afecta
	//forall (i in I, l not in N[i]) z[<i,l>] == 1;
	//forall (i in I, Ising (l in N[i]) == 0) z[<i,l>] == 1;
	forall (i in I, l in NOT_N[i]) z[<i,l>] == 1;
	
	// 7. Define cuantos clientes se pierden en caso de que se destruya la antena l
	//forall (l in J) v_l[l] == sum (i in I : l in N[i]) (w[i] * (1 - z[<i,l>]));
//	forall (l in J) v_l[l] == sum (i in I : l in N[i]) (w[i] * (1 - z[<i,l>]));
	forall (l in J) v_l[l] == sum (i in I : l in N[i]) (w[i] * (1 - z[<i,l>]));
	
	// 8. Define v
	// Restriccion especial si se elige la segunda funcion objetivo.
	forall (l in J) v >= v_l[l];
	
	// 9. Fuerza la separacion minima entre antenas
	forall (j in J, k in M[j]) y[k] + y[j] <= 1;
};

//
// Mostrar datos
execute ver_resultado{
  var tot_personas = 0;
  var tot_pers_todas_antenas = 0;
  var tot_pers_antenas_reforzadas = 0;
  var tot_pers_worst_reforzadas = 0;
  var tot_pers_average_reforzadas = 0;
  
  var max_v_l = 0;
  var sum_v_l = 0;
  
  var i, j, l;
  var str_aux = "";
  
  writeln();  
  writeln();  

// Numero de antenas reforzadas, p 
  writeln("Numero de antenas reforzadas, p = ", p);

// numero total de personas en el territorio 
  for(i in I){
    tot_personas = tot_personas + w[i];
  }
  writeln("Numero total de personas en el territorio: ", tot_personas);

  // Numero de clientes cubiertos por todas las antenas (reforzadas y no reforzadas)
  // numero de personas cubiertas con las antenas elegidas
  // sum (i in I) w[i] * x[i]
  for(i in I){
	 if (N[i].size != 0) {
	  tot_pers_todas_antenas = tot_pers_todas_antenas + w[i];   	
	 //} else {
	 //  writeln("N[", i, "] = {}");
	 }
  }
  writeln("Numero total de personas cubiertas por TODAS las antenas: ", tot_pers_todas_antenas);
  
  writeln("-----------------------------------------");
  writeln("Numero total de clientes cubiertos por las antenas reforzadas: ");
// numero total de clientes cubiertos por las antenas reforzadas
  for(i in I){
    tot_pers_antenas_reforzadas = tot_pers_antenas_reforzadas + w[i] * x[i];
  }
  writeln("   1. Total: ", tot_pers_antenas_reforzadas);
  
// numero total de clientes cubiertos por las antenas reforzadas 
// cuando se elimina la antena reforzada de mayor servicio a clientes
  tot_pers_worst_reforzadas = tot_pers_antenas_reforzadas - v
  // writeln("   2. Perdida una antena (peor caso): ", tot_pers_worst_reforzadas);
  
  // Se halla el valor de v dentro del conjunto v_l de antenas reforzadas
  max_v_l = 0;
  for(j in J){
  	if (max_v_l < v_l[j] * y[j]) {
  		max_v_l = v_l[j];
  	}
  }
  //writeln("        v = ", v);
  //writeln("        v (verdadera) = max_v_l = ", max_v_l);
  tot_pers_worst_reforzadas = tot_pers_antenas_reforzadas - max_v_l
  writeln("   2. Perdida una antena (peor caso): ", tot_pers_worst_reforzadas);
  
  
// numero total de clientes cubiertos por las antenas reforzadas 
// cuando se elimina una antena y se deja de computar a 
// la media de clientes cubiertos por las antenas reforzadas
  for(l in J){
//    sum_v_l = sum_v_l + v_l[l];
    sum_v_l = sum_v_l + v_l[l] * y[l];
  }
  tot_pers_average_reforzadas = tot_pers_antenas_reforzadas - sum_v_l/p
  
  writeln("   3. Perdida una antena (caso intermedio): ", tot_pers_average_reforzadas);

  // Lista de antenas reforzadas con numero de clientes que cubren
  str_aux = "";
  for(j in J){
  	if (y[j] == 1)  {
	  str_aux = str_aux + " " + j + ", v_l: " + v_l[j] + ". ";
	}	
  }
  // writeln("Lista de antenas reforzadas = {", str_aux, "}");
  
  writeln("-----------------------------------------");

  str_aux = "";
  // Lista de antenas reforzadas 
  for(j in J){
  	if (y[j] == 1)  {
	  str_aux = str_aux + " " + j;
	}	
  }
  writeln("Lista de antenas reforzadas = {", str_aux, "}");
  
  // Razon tot_pers_antenas_reforzadas/tot_pers_todas_antenas
  writeln("Porcentaje personas cubiertas: ", 
  			100 * tot_pers_antenas_reforzadas/tot_pers_todas_antenas, " %");
}
