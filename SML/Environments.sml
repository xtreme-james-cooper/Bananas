
(* our environments have three parts: 
   the expressions, the values (eg, val_decls), and the types 
   They also come in static and dynamic versions
   static maps expr names to type -> type, value names to type list -> type, and type names to functors
   dynamic maps expr names to expr lists, value names to val_decls, and type names to functors *)

exception MissingType of name
exception MissingVal of name
exception MissingExpr of name

type static_environment = {
  var_e_type : (name, typ * typ) assoc,
  var_v_type : (name, typ list * typ) assoc,
  var_t_type : (name, funct) assoc
}

type dynamic_environment = {
  var_e_bind: (name, expr list) assoc,
  var_v_bind: (name, vall list -> vall) assoc,
  var_t_bind: (name, funct) assoc
}

(* a whole bunch of utility getters and setters and empty versions *)

val empty_static = { var_e_type = [], var_v_type = [], var_t_type = [] }

fun extend_e_static x t (gamma: static_environment) = { 
    var_e_type = (x, t) :: #var_e_type gamma,
    var_v_type = #var_v_type gamma,
    var_t_type = #var_t_type gamma }

fun extend_t_static x t (gamma: static_environment) = { 
    var_e_type = #var_e_type gamma,
    var_v_type = #var_v_type gamma,
    var_t_type = (x, t) :: #var_t_type gamma }

fun combine_static (gamma1: static_environment) (gamma2: static_environment) = { 
    var_e_type = #var_e_type gamma1 @ #var_e_type gamma2, 
    var_v_type = #var_v_type gamma1 @ #var_v_type gamma2, 
    var_t_type = #var_t_type gamma1 @ #var_t_type gamma2 }

fun var_e_type (gamma: static_environment) x = lookup x (#var_e_type gamma) MissingExpr
fun var_v_type (gamma: static_environment) x = lookup x (#var_v_type gamma) MissingVal
fun var_t_type (gamma: static_environment) x = lookup x (#var_t_type gamma) MissingType

val empty_dynamic = { 
      var_e_bind = [], 
      var_v_bind = [], 
      var_t_bind = [] }

fun extend_e_dynamic x e (lam: dynamic_environment) = { 
    var_e_bind = (x, e) :: #var_e_bind lam,
    var_v_bind = #var_v_bind lam,
    var_t_bind = #var_t_bind lam }

fun extend_t_dynamic x t (lam: dynamic_environment) = { 
    var_e_bind = #var_e_bind lam,
    var_v_bind = #var_v_bind lam,
    var_t_bind = (x, t) :: #var_t_bind lam }

fun combine_dynamic (lam1: dynamic_environment) (lam2: dynamic_environment) = { 
    var_e_bind = #var_e_bind lam1 @ #var_e_bind lam2, 
    var_v_bind = #var_v_bind lam1 @ #var_v_bind lam2, 
    var_t_bind = #var_t_bind lam1 @ #var_t_bind lam2 }

fun var_e_bind (lam: dynamic_environment) x = lookup x (#var_e_bind lam) MissingExpr
fun var_v_bind (lam: dynamic_environment) x = lookup x (#var_v_bind lam) MissingVal
fun var_t_bind (lam: dynamic_environment) x = lookup x (#var_t_bind lam) MissingType