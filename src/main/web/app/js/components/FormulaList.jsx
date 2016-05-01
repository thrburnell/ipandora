import React from 'react'
import Formula from './Formula'

const FormulaList = ({ heading, formulas }) => (
  <div>
    <h2>{ heading }</h2>
    { formulas.map(formula =>
      <Formula
        key={formula.id}
        {...formula}
      />
    )}
  </div>
)

export default FormulaList

