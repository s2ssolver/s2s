#[derive(Debug, Clone)]
struct Normalized {
    expr: Rc<Expression>,
    side_conditions: Vec<Rc<Expression>>,
    additional_vars: Vec<Rc<Variable>>,
}

impl Normalized {
    pub fn new(
        expr: Rc<Expression>,
        side_conditions: Vec<Rc<Expression>>,
        additional_vars: Vec<Rc<Variable>>,
    ) -> Self {
        Self {
            expr,
            side_conditions,
            additional_vars,
        }
    }

    pub fn combine(self, other: Normalized, expr: Rc<Expression>) -> Normalized {
        let mut side_conditions = self.side_conditions;
        side_conditions.extend(other.side_conditions);
        let mut additional_vars = self.additional_vars;
        additional_vars.extend(other.additional_vars);
        Normalized::new(expr, side_conditions, additional_vars)
    }

    pub fn combine_all(norms: Vec<Normalized>, expr: Rc<Expression>) -> Normalized {
        let mut side_conditions = Vec::new();
        let mut additional_vars = Vec::new();
        for n in norms.iter() {
            side_conditions.extend(n.side_conditions.iter().cloned());
            additional_vars.extend(n.additional_vars.iter().cloned());
        }
        Normalized::new(expr, side_conditions, additional_vars)
    }

    pub fn with_expr(self, expr: Rc<Expression>) -> Normalized {
        Normalized::new(expr, self.side_conditions, self.additional_vars)
    }
}

impl From<Rc<Expression>> for Normalized {
    fn from(expr: Rc<Expression>) -> Self {
        Self {
            expr,
            side_conditions: Vec::new(),
            additional_vars: Vec::new(),
        }
    }
}

/// Rewrites the script such that it contains only supported constructs.
/// After this call, the script is in Boolean normal form.
pub fn rewrite(
    script: &Script,
    builder: &mut ExpressionBuilder,
    ctx: &mut Context,
) -> Result<Script, NormalizationError> {
    let normalized = script
        .iter_asserts()
        .map(|assert| normalize_expression(assert, builder, ctx, true))
        .collect::<Result<Vec<Normalized>, NormalizationError>>()?;

    let mut new_script = Script::default();
    let mut num_asserts = 0;
    for cmd in script.iter() {
        match cmd {
            SmtCommand::Assert(_) => {
                let normalized_assertion = normalized.get(num_asserts).unwrap();
                for v in normalized_assertion.additional_vars.iter() {
                    new_script.declare_var(v.clone());
                }
                new_script.assert(normalized_assertion.expr.clone());
                for sc in normalized_assertion.side_conditions.iter() {
                    new_script.assert(sc.clone());
                }
                num_asserts += 1;
            }
            SmtCommand::CheckSat => new_script.check_sat(),
            SmtCommand::DeclareConst(v) => new_script.declare_var(v.clone()),
            SmtCommand::Exit => new_script.exit(),
            SmtCommand::GetModel => new_script.get_model(),
            SmtCommand::SetLogic(l) => new_script.set_logic(l.clone()),
        }
    }
    Ok(new_script)
}

fn normalize_expression(
    expr: &Rc<Expression>,
    builder: &mut ExpressionBuilder,
    ctx: &mut Context,
    pol: bool,
) -> Result<Normalized, NormalizationError> {
    match expr.get_type() {
        ExprType::Core(c) => normalize_core_expression(c, builder, ctx, pol),
        ExprType::String(s) => normalize_string_expression(s, builder, ctx, pol),
        ExprType::Int(i) => normalize_int_expression(i, builder, ctx, pol),
    }
}

fn normalize_core_expression(
    expr: &CoreExpr,
    builder: &mut ExpressionBuilder,
    ctx: &mut Context,
    pol: bool,
) -> Result<Normalized, NormalizationError> {
    match expr {
        CoreExpr::Bool(b) => Ok(builder.bool(*b).into()),
        CoreExpr::Var(v) => {
            let e = builder.var(v.clone());
            Ok(e.into())
        }
        CoreExpr::Not(r) => {
            let normal = normalize_expression(r, builder, ctx, !pol)?;
            let expr = builder.not(normal.expr.clone());
            Ok(normal.with_expr(expr))
        }
        CoreExpr::And(rs) => {
            let normal = rs
                .iter()
                .map(|r| normalize_expression(r, builder, ctx, pol))
                .collect::<Result<Vec<Normalized>, NormalizationError>>()?;
            let conj = builder.and(normal.iter().map(|n| n.expr.clone()).collect());
            Ok(Normalized::combine_all(normal, conj))
        }
        CoreExpr::Or(rs) => {
            let normal = rs
                .iter()
                .map(|r| normalize_expression(r, builder, ctx, pol))
                .collect::<Result<Vec<Normalized>, NormalizationError>>()?;
            let disj = builder.or(normal.iter().map(|n| n.expr.clone()).collect());
            Ok(Normalized::combine_all(normal, disj))
        }
        CoreExpr::Equal(l, r) => {
            match (l.sort(), r.sort()) {
                (Sort::Bool, Sort::Bool) => {
                    // Rewrite to l -> r and r -> l
                    let l2r = builder.imp(l.clone(), r.clone());
                    let r2l = builder.imp(r.clone(), l.clone());
                    let conj = builder.and(vec![l2r, r2l]);
                    normalize_expression(&conj, builder, ctx, pol)
                }
                (s1, s2) if s1 == s2 => {
                    let l = normalize_expression(l, builder, ctx, pol)?;
                    let r = normalize_expression(r, builder, ctx, pol)?;
                    let eq = builder.eq(l.expr.clone(), r.expr.clone());
                    Ok(Normalized::combine(l, r, eq))
                }
                (s1, s2) => Err(NormalizationError::InvalidSort {
                    expr: builder.eq(l.clone(), r.clone()),
                    expected: s1,
                    got: s2,
                }),
            }
        }
        CoreExpr::Imp(l, r) => {
            // Rewrite to !l or r
            let l = builder.not(l.clone());
            let norm = builder.or(vec![l, r.clone()]);
            normalize_expression(&norm, builder, ctx, pol)
        }
        CoreExpr::Ite(_i, _t, _e) => {
            let (v, conds) = rewrite_ite(_i.clone(), _t.clone(), _e.clone(), ctx, builder)?;
            let mut additional_vars = vec![v.clone()];
            let mut side_conditions = Vec::new();
            for c in conds {
                let norm = normalize_expression(&c, builder, ctx, pol)?;
                side_conditions.push(norm.expr);
                additional_vars.extend(norm.additional_vars);
            }
            Ok(Normalized::new(
                builder.var(v),
                side_conditions,
                additional_vars,
            ))
        }
        CoreExpr::Distinct(_) => Err(NormalizationError::Unsupported(expr.to_string())),
    }
}

fn rewrite_ite(
    i: Rc<Expression>,
    t: Rc<Expression>,
    e: Rc<Expression>,
    ctx: &mut Context,
    builder: &mut ExpressionBuilder,
) -> Result<(Rc<Variable>, Vec<Rc<Expression>>), NormalizationError> {
    // Create new variable T, i -> T = t, !i -> T = e, return T

    let sort = if t.sort() == e.sort() {
        t.sort()
    } else {
        return Err(NormalizationError::InvalidSort {
            expr: builder.ite(i.clone(), t.clone(), e.clone()),
            expected: t.sort(),
            got: e.sort(),
        });
    };
    let v = ctx.new_temp_var(sort);
    let vv = builder.var(v.clone());

    let eq_then = builder.eq(vv.clone(), t);
    let eq_else = builder.eq(vv, e);

    let then = builder.imp(i.clone(), eq_then);
    let neg_i = builder.not(i);
    let else_ = builder.imp(neg_i, eq_else);

    return Ok((v, vec![then, else_]));
}

fn normalize_string_expression(
    expr: &StrExpr,
    builder: &mut ExpressionBuilder,
    ctx: &mut Context,
    pol: bool,
) -> Result<Normalized, NormalizationError> {
    match expr {
        StrExpr::Constant(_) | StrExpr::Regex(_) => Ok(builder.string_expr(expr.clone()).into()),
        StrExpr::Concat(rs) => {
            let normal = rs
                .iter()
                .map(|r| normalize_expression(r, builder, ctx, pol))
                .collect::<Result<Vec<Normalized>, NormalizationError>>()?;
            // TODO: Assert all of sort String
            let concat = builder.concat(normal.iter().map(|n| n.expr.clone()).collect());
            Ok(Normalized::combine_all(normal, concat))
        }
        StrExpr::Length(l) => {
            let normal = normalize_expression(l, builder, ctx, pol)?;
            // TODO: Assert sort String
            let expr = builder.length(normal.expr.clone());
            Ok(normal.with_expr(expr))
        }
        StrExpr::InRe(l, re) => {
            let l = normalize_expression(l, builder, ctx, pol)?;
            let re = normalize_expression(re, builder, ctx, pol)?;
            // TODO: Assert sort String and Regex
            let norm = builder.in_re(l.expr.clone(), re.expr.clone());
            Ok(Normalized::combine(l, re, norm))
        }
        StrExpr::Substr(w, i, l) => {
            let rewritten = rewrite_substr(w.clone(), i.clone(), l.clone())?;
            normalize_expression(&rewritten, builder, ctx, pol)
        }
        StrExpr::At(w, i) => {
            let rewritten = rewrite_str_at(w.clone(), i.clone())?;
            normalize_expression(&rewritten, builder, ctx, pol)
        }
        StrExpr::PrefixOf(l, r) => {
            let rewritten = rewrite_prefix_of(l.clone(), r.clone(), ctx, builder, pol)?;
            normalize_expression(&rewritten, builder, ctx, pol)
        }
        StrExpr::SuffixOf(l, r) => {
            let rewritten = rewrite_suffix_of(l.clone(), r.clone(), ctx, builder, pol)?;
            normalize_expression(&rewritten, builder, ctx, pol)
        }
        StrExpr::Contains(l, r) => {
            let rewritten = rewrite_contains(l.clone(), r.clone(), builder, ctx, pol)?;
            normalize_expression(&rewritten, builder, ctx, pol)
        }
        _ => Err(NormalizationError::Unsupported(expr.to_string())),
    }
}

fn rewrite_substr(
    w: Rc<Expression>,
    i: Rc<Expression>,
    l: Rc<Expression>,
) -> Result<Rc<Expression>, NormalizationError> {
    return Err(NormalizationError::Unsupported(
        StrExpr::Substr(w, i, l).to_string(),
    ));
}

fn rewrite_str_at(
    w: Rc<Expression>,
    i: Rc<Expression>,
) -> Result<Rc<Expression>, NormalizationError> {
    return Err(NormalizationError::Unsupported(
        StrExpr::At(w, i).to_string(),
    ));
}

fn rewrite_prefix_of(
    prefix: Rc<Expression>,
    of: Rc<Expression>,
    ctx: &mut Context,
    builder: &mut ExpressionBuilder,
    pol: bool,
) -> Result<Rc<Expression>, NormalizationError> {
    if let ExprType::String(StrExpr::Constant(prefix)) = prefix.get_type() {
        // regular suffix constraint
        let all = builder.re_builder().all();
        let pref = builder.re_builder().word(prefix.clone().into());
        let re = builder.re_builder().concat(vec![pref, all]);
        let re = builder.regex(re);
        Ok(builder.in_re(of, re))
    } else if pol {
        let w2 = ctx.new_temp_var(Sort::String);
        let w2 = builder.var(w2);
        let rhs = builder.concat(vec![prefix.clone(), w2]);
        Ok(builder.eq(of, rhs))
    } else {
        Err(NormalizationError::InvalidNegationQuantifier(
            builder.prefix_of(prefix, of).to_string(),
        ))
    }
}

fn rewrite_suffix_of(
    suffix: Rc<Expression>,
    of: Rc<Expression>,
    ctx: &mut Context,
    builder: &mut ExpressionBuilder,
    pol: bool,
) -> Result<Rc<Expression>, NormalizationError> {
    if let ExprType::String(StrExpr::Constant(suffix)) = suffix.get_type() {
        // regular suffix constraint
        let all = builder.re_builder().all();
        let suff = builder.re_builder().word(suffix.clone().into());
        let re = builder.re_builder().concat(vec![all, suff]);
        let re = builder.regex(re);
        Ok(builder.in_re(of, re))
    } else if pol {
        let w2 = ctx.new_temp_var(Sort::String);
        let w2 = builder.var(w2);
        let rhs = builder.concat(vec![w2, suffix.clone()]);
        Ok(builder.eq(of, rhs))
    } else {
        Err(NormalizationError::InvalidNegationQuantifier(
            builder.suffix_of(suffix, of).to_string(),
        ))
    }
}

fn rewrite_contains(
    w: Rc<Expression>,
    c: Rc<Expression>,
    builder: &mut ExpressionBuilder,
    ctx: &mut Context,
    pol: bool,
) -> Result<Rc<Expression>, NormalizationError> {
    if let ExprType::String(StrExpr::Constant(contains)) = c.get_type() {
        // regular suffix constraint
        let all = builder.re_builder().all();
        let cont = builder.re_builder().word(contains.clone().into());
        let re = builder.re_builder().concat(vec![all.clone(), cont, all]);
        let re = builder.regex(re);
        Ok(builder.in_re(w, re))
    } else if pol {
        let w2 = ctx.new_temp_var(Sort::String);
        let w2 = builder.var(w2);
        let w3 = ctx.new_temp_var(Sort::String);
        let w3 = builder.var(w3);
        let rhs = builder.concat(vec![w2, c, w3]);
        Ok(builder.eq(w, rhs))
    } else {
        Err(NormalizationError::InvalidNegationQuantifier(
            builder.contains(w, c).to_string(),
        ))
    }
}

fn normalize_int_expression(
    expr: &IntExpr,
    builder: &mut ExpressionBuilder,
    ctx: &mut Context,
    pol: bool,
) -> Result<Normalized, NormalizationError> {
    let norm: Normalized = match expr {
        IntExpr::Constant(_) => builder.int_expr(expr.clone()).into(),
        IntExpr::Add(rs) => {
            let normal = rs
                .iter()
                .map(|r| normalize_expression(r, builder, ctx, pol))
                .collect::<Result<Vec<Normalized>, NormalizationError>>()?;
            let expr = builder.add(normal.iter().map(|n| n.expr.clone()).collect());
            Normalized::combine_all(normal, expr)
        }
        IntExpr::Sub(l, r) => {
            let l = normalize_expression(l, builder, ctx, pol)?;
            let r = normalize_expression(r, builder, ctx, pol)?;
            let expr = builder.sub(l.expr.clone(), r.expr.clone());
            Normalized::combine_all(vec![l, r], expr)
        }
        IntExpr::Mul(rs) => {
            let normal = rs
                .iter()
                .map(|r| normalize_expression(r, builder, ctx, pol))
                .collect::<Result<Vec<Normalized>, NormalizationError>>()?;
            let expr = builder.mul(normal.iter().map(|n| n.expr.clone()).collect());
            Normalized::combine_all(normal, expr)
        }
        IntExpr::Div(l, r) => {
            let l = normalize_expression(l, builder, ctx, pol)?;
            let r = normalize_expression(r, builder, ctx, pol)?;
            let expr = builder.div(l.expr.clone(), r.expr.clone());
            Normalized::combine_all(vec![l, r], expr)
        }
        IntExpr::Mod(l, r) => {
            let l = normalize_expression(l, builder, ctx, pol)?;
            let r = normalize_expression(r, builder, ctx, pol)?;
            let expr = builder.mod_(l.expr.clone(), r.expr.clone());
            Normalized::combine_all(vec![l, r], expr)
        }
        IntExpr::Neg(e) => {
            let e = normalize_expression(e, builder, ctx, pol)?;
            let expr = builder.neg(e.expr.clone());
            e.with_expr(expr)
        }
        IntExpr::Abs(r) => {
            let r = normalize_expression(r, builder, ctx, pol)?;
            let expr = builder.abs(r.expr.clone());
            r.with_expr(expr)
        }
        IntExpr::Le(l, r) => {
            let l = normalize_expression(l, builder, ctx, pol)?;
            let r = normalize_expression(r, builder, ctx, pol)?;
            let expr = builder.le(l.expr.clone(), r.expr.clone());
            Normalized::combine_all(vec![l, r], expr)
        }
        IntExpr::Lt(l, r) => {
            let l = normalize_expression(l, builder, ctx, pol)?;
            let r = normalize_expression(r, builder, ctx, pol)?;
            let expr = builder.lt(l.expr.clone(), r.expr.clone());
            Normalized::combine_all(vec![l, r], expr)
        }
        IntExpr::Ge(l, r) => {
            let l = normalize_expression(l, builder, ctx, pol)?;
            let r = normalize_expression(r, builder, ctx, pol)?;
            let expr = builder.ge(l.expr.clone(), r.expr.clone());
            Normalized::combine_all(vec![l, r], expr)
        }
        IntExpr::Gt(l, r) => {
            let l = normalize_expression(l, builder, ctx, pol)?;
            let r = normalize_expression(r, builder, ctx, pol)?;
            let expr = builder.gt(l.expr.clone(), r.expr.clone());
            Normalized::combine_all(vec![l, r], expr)
        }
    };
    Ok(norm)
}
